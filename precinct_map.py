"""
This script creates an html folium map of WA-08 with layers
showing precincts, counties, legislative districts, staging locations, 
organizing turfs, heat map of turnout targets, addresses of frequent canvassars, 
door-knocking completion, and search bars. 

To create the map, run:
    python3 precinct_map.py
Or, if you want to use custom inputs:
    python3 precinct_map.py
        --precinct_shapefile_filepath="{precinct shapefile filepath}" 
        --map_filepath="{filepath for where map will be saved on local computer}"
"""

#~~~~~~ Setup ~~~~~~#
from itertools import count
from turtle import fillcolor
from xml.etree.ElementPath import ops
import geopandas as gpd
import json
import zipfile
import io
from fiona.io import ZipMemoryFile
import matplotlib.pyplot as plt
import geopy
from numpy import NaN
import pandas as pd
import folium
import mapclassify
from shapely import ops
from shapely.geometry.polygon import Polygon
from shapely.geometry.multipolygon import MultiPolygon
import json
import re
import branca
from geopy.geocoders import Nominatim
from parsons import GoogleSheets
import os
import logging
import gitlab
import click

#~~~~~~ Set up logging ~~~~~~~#
logger = logging.getLogger(__name__)
_handler = logging.StreamHandler()
_formatter = logging.Formatter(('%(levelname)s %(message)s'))
_handler.setFormatter(_formatter)
logger.addHandler(_handler)
logger.setLevel('INFO')

#~~~~~~ Generate Base GeoDataframe ~~~~~~#
"""
These functions compile the base geodataframe for the resulting map
by merging the precinct shpefile with data assigning each precinct
to an organizer region (A, B, C, D, E) 
"""

def unzip_to_gdf(filepath):
    """
    Converts shapefile to a geodataframe

    Args
        file_path: str
            The filepath for the shapefile
    
    Returns
        geodataframe
    """
    zipshp = io.BytesIO(open(filepath, 'rb').read())
    with (ZipMemoryFile(zipshp)) as memfile:
        with memfile.open() as src:
            crs = src.crs 
            gdf = gpd.GeoDataFrame.from_features(src, crs = crs)
    return gdf

def prec_shapefile_to_geodataframe(precinct_shapefile_filepath):
    """
    Convert precinct shapefile to geodataframe

    Args
        precinct_shapefile_filepath: str
            The filepath for the precinct shapefile
    
    Returns
        geodataframe
    """
    precincts = unzip_to_gdf(precinct_shapefile_filepath)
    precincts.rename(columns = {'van_prec_i': 'van_precinct_id', 'van_prec_n':'VAN Precinct Name', 'c_name':'County'}, inplace = True)
    precincts.van_precinct_id = precincts.van_precinct_id.astype(str)
    return precincts

def get_organizer_assignment(sheets):
    """
    Creates dataframe of organizer and region number assignment to each precinct

    Arg 
        sheets: Google Sheets
            Instantiated google sheet class
    
    Returns
        dataframe
    """

    # The district is split into numbered regions (1-10).
    # Here, we are pulling the number assignment for each precinct from a gsheet (which are updated by Organizing Director)
    gsheet_id = '1rH62dKf9STLpgvf_xO2ruzc6cWLJFeO9v4ANDofUyy0'
    number_assignment_raw = sheets.get_worksheet(gsheet_id, worksheet=0).to_dataframe().iloc[:, :4]
    number_assignment_cleaned = pd.DataFrame(number_assignment_raw.iloc[1:, :])
    number_assignment_cleaned.columns = number_assignment_raw.iloc[0, 0:]
    number_assignment_cleaned = number_assignment_cleaned.reset_index(drop = True).drop(['SSD','SHD'], axis = 1)
    number_assignment_cleaned.rename(columns = {'VAN Turf' : 'Turf', 'VAN Precinct ID':'van_precinct_id'}, inplace = True)
    
    # The ten numbered regions are then split between organizing teams A-E
    # Here, we are pulling the organizing team assignment for each numbered region from the same ghseet   
    organizer_assignment_raw = sheets.get_worksheet(gsheet_id, worksheet=1).to_dataframe().iloc[:, :2]
    organizer_assignment_cleaned = pd.DataFrame(organizer_assignment_raw.iloc[1:, :]).reset_index(drop = True)
    organizer_assignment_cleaned.columns = organizer_assignment_raw.iloc[0]
    
    # Here, we merge the numbered assignment with the organizing team assignment
    organizer_number_assignment = number_assignment_cleaned.merge(organizer_number_assignment, how = 'left', on = 'Turf')
    
    return organizer_number_assignment

def generate_organizer_assignment_gdf(precincts, organizer_assignment):
    """
    Merges the precinct geodataframe with the organizer/number assignment

    Arg
        precincts: gdf
            precinct geodataframe
        
        organizer_assignmnet: df
            organizer and region number assignment
    
    Returns
        geodataframe
    """

    precincts_assigned = precincts.merge(organizer_assignment, how = 'left', on = 'van_precinct_id')
    precincts_assigned_drop_na = precincts_assigned[~precincts_assigned.geometry.isna()]
    precincts_assigned_drop_na.set_crs('epsg:3857', inplace = True).to_crs('epsg:4326', inplace = True)
    
    return precincts_assigned_drop_na

#~~~~~~~~~ Generate Additional Map Layers ~~~~~~~~~#
"""
These functions generate additional map layers using 
the base geodataframe.
"""

def group_by_col(precincts_assigned, col_name):
    """
    Groups and aggregates the precinct geodataframe by a given column name and
    produce geodataframes for additional organizer, numerical region, legislative
    district, and county level maps

    Arg
        precincts_assigned: gdf
            precinct assigned to organizers geodataframe 
        
        col_name: column to groupby
            organizer and region number assignment
    
    Returns
        geodataframe
    """

    # create dictionary to aggregate the geometry column together
    # and combine strings in other columns to create aggregated lists
    agg_string_columns = lambda row: ', '.join(row.drop_duplicates().dropna().astype(str))
    agg_dic = {'geometry':ops.unary_union, 'Organizer':agg_string_columns, 'Turf':agg_string_columns, 'County':agg_string_columns, 'LD':agg_string_columns}
    
    # group by given column name and apply the aggregation functions
    # and generate resulting geodataframe
    precincts_grouped = precincts_assigned.groupby(col_name).agg(agg_dic)
    precincts_grouped.drop(columns = [col_name], inplace = True)
    precincts_grouped.reset_index(inplace = True)
    precincts_grouped.set_geometry(col='geometry', inplace=True)
    precincts_grouped.set_crs('epsg:4326', inplace = True)

    return precincts_grouped

def generate_staging_location_gdf(sheets,precincts_assigned):
    """
    Generates the geodataframe for staging location map layer

    Arg:

        sheets: GoogleSheets
            Instantaited GoogleSheets class

        precincts_assigned: gdf
            precinct assigned to organizers geodataframe
        
    Returns:
        geodataframe
    """
    gsheet_id = '1PS7VWdefRnyp4iX9c0EfHB7pu3wbsIsjBDn094cHpJk'

    worksheet = 'staging_location_assignment'

    # Retrieve precinct-staging location assignment information from gsheet
    sl_turnout = sheets.get_worksheet(gsheet_id, worksheet=worksheet).to_dataframe()
    sl_turnout.van_precinct_id = sl_turnout.van_precinct_id.astype(str)

    # Merge precinct shapefile with precinct-staging location assignment dataframe
    sl_turnout_gdf = precincts_assigned.merge(sl_turnout, how='right', on='van_precinct_id')
    sl_turnout_drop_na = sl_turnout_gdf[~sl_turnout_gdf.geometry.isna()]

    # Group and aggregate shapefile to produce staging location-level geodataframe 
    agg_func = lambda row: ', '.join(row.drop_duplicates().dropna().astype(str))
    gdf_sl = sl_turnout_drop_na.groupby('staging_loc').agg({'geometry': ops.unary_union, 'County' : agg_func, 'LD': agg_func})
    df_sub = pd.DataFrame(sl_turnout.groupby('staging_loc').sum(['total_people', 'total_households'])).reset_index()
    gdf_sl = gdf_sl.reset_index()
    gdf_sl = gdf_sl.merge(df_sub, on = 'staging_loc')
    gdf_sl = gdf_sl.set_geometry(col='geometry')
    gdf_sl.set_crs('epsg:4326', inplace = True)

    return gdf_sl

def generate_turnout_completion_gdf(sheets, precincts_assigned):
    """
    Generates geodataframe for map layer to track percentage door knocking completion
    per precinct

    Arg

        sheets: GoogleSheets
            Instantaited GoogleSheets class

        precincts_assigned: gdf
            precinct geodataframe

    Returns
        gdf
    """

    gsheet_id = '1uBzWnBHxzaiJcA3IqVX3b1mHDoUfe72VNLhNimSQykg'
    worksheet = 'turnout_completion'

    # Retrieve turnout completion data from gsheet
    turnout_completion = sheets.get_worksheet(gsheet_id, worksheet=worksheet).to_dataframe()
    turnout_completion.van_precinct_id = turnout_completion.van_precinct_id.astype(str)

    # Merge turnout completion data with precinct shapefile 
    turnout_completion_gdf = precincts_assigned.merge(turnout_completion, how = 'left', on = 'van_precinct_id')
    turnout_completion_gdf['percentage_not_attempted'] = turnout_completion_gdf['percentage_not_attempted'].astype(float)
    turnout_completion_gdf['percentage_not_attempted_nv'] = turnout_completion_gdf['percentage_not_attempted_nv'].astype(float)

    return turnout_completion_gdf

def generate_freq_vol_gdf(sheets):
    """
    Generates geodataframe for map layer plotting most frequent canvassars

    Arg

        sheets: GoogleSheets
            Instantaited GoogleSheets class

    Returns
        gdf
    """

    gsheet_id = '1uBzWnBHxzaiJcA3IqVX3b1mHDoUfe56VNLhNimSQyni'
    worksheet = 'volunteer_addresses'

    # Retrieve data from gsheet containing percentage door-knock completion data from gsheet
    addresses = sheets.get_worksheet(gsheet_id, worksheet=worksheet).to_dataframe()
    addresses['myc_van_id'] = addresses['myc_van_id'].astype(str)

    # Create gdf for volunteers with geocoded addresses
    addresses_with_lat_lon = addresses[addresses.latitude != '0']
    addresses_gdf = gpd.GeoDataFrame(addresses_with_lat_lon, geometry=gpd.points_from_xy(addresses_with_lat_lon.longitude, addresses_with_lat_lon.latitude, crs="EPSG:4326"))
    addresses_gdf.to_crs('epsg:4326', inplace = True)

    # Geocode addresses without geocoded addresses and create gdf
    addresses_to_geocode = addresses[(addresses.latitude == '0') & (addresses.address_exists == '1')]
    geopy.geocoders.options.default_user_agent = "sharine@drkimschrier.com"
    addresses_geocoded_1 = gpd.tools.geocode(addresses_to_geocode.address.str.cat([addresses_to_geocode['state'], addresses_to_geocode['zip'].astype(str)], ', '), provider=Nominatim)
    addresses_geocoded_cleaned_1 = addresses_geocoded_1[~addresses_geocoded_1['geometry'].is_empty]
    addresses_geocoded_cleaned_1.to_crs('epsg:4326', inplace = True)
    addresses_gdf_sub_1 = addresses_geocoded_cleaned_1.merge(addresses_to_geocode, left_index=True, right_index=True)
    addresses_gdf_sub_1.drop(['address_x', 'address_y'], axis = 1, inplace = True)

    # Geocode cities for volunteers without addresses and create gdf
    cities_to_geocode = addresses[(addresses.latitude == '0') & (addresses.address_exists == '0')]
    addresses_geocoded_2 = gpd.tools.geocode((cities_to_geocode['city'].str.cat([cities_to_geocode['state'], cities_to_geocode['zip'].astype(str)], ', ')), provider=Nominatim)
    addresses_geocoded_cleaned_2 = addresses_geocoded_2[~addresses_geocoded_2['geometry'].is_empty]
    addresses_geocoded_cleaned_2.to_crs('epsg:4326', inplace = True)
    addresses_gdf_sub_2= addresses_geocoded_cleaned_2.merge(cities_to_geocode, left_index=True, right_index=True)
    addresses_gdf_sub_2.drop(['address_x', 'address_y'], axis = 1, inplace = True)

    # Merge all geodataframes from above
    addresses_gdf = gpd.GeoDataFrame(pd.concat([addresses_gdf, addresses_gdf_sub_1, addresses_gdf_sub_2], ignore_index=True), crs = addresses_gdf.crs)

    return addresses_gdf

#~~~~~~~~~ Create final map ~~~~~~~~~~#
"""
This function create the Folium html map
"""

def to_map(map_filepath, organizer, counties, ld, addresses, staging_location, precincts, turnout_completion):
    """
    Generates the layers of the Folium html map

    Arg
        organizer: gdf
            generated gdf of district split into organizer regions
        counties: gdf
            generated gdf of district split into counties
        ld: gdf
            generated gdf of district split into legislative districts
        addresses: gdf
            generated gdf of frequent volunteeer addresses
        staging_location: gdf
            generated gdf of district split into staging locations
        precicnts: gdf
            generated gdf of precincts
        turnout_completion: gdf
            generated gdf of door knocking completion for each precinct

    Return
        html file
    """

    # Generate map layer showing outline of organizer regions
    map = organizer.explore(name = 'Organizers Outline',
                        column = 'Organizer',
                        legend = False,
                        show = False,
                        cmap = 'Set1',
                        style_kwds= {'weight': '3.5', 'fillOpacity': 0.0},
                        highlight_kwds = {'fillOpacity': 0.5},
                        tooltip = ['Organizer', 'Turf'],
                        popup = ['Organizer', 'Turf', "County", 'LD', 'Total Precincts'])
    
    # Generate map layer showing organizer regions filled
    organizer.explore(name = 'Organizers Filled',
                        column = 'Organizer',
                        legend = True,
                        show = False,
                        cmap = 'Set1',
                        highlight_kwds = {'fillOpacity': 0.5},
                        tooltip = ['Organizer', 'Turf'],
                        popup = ['Organizer', 'Turf', "County", 'LD', 'Total Precincts'],
                        m = map)
    
    # Generate map layer showing counties
    counties.explore(name = 'Counties',
                    show = False,
                    column = 'County',
                    cmap = 'Paired',
                    tooltip = ['County'],
                    popup = ['County', 'LD', 'Organizer', 'Turf', 'Total Precincts'],
                    style_kwds= {'stroke': False, 'fillOpacity': 0.45},
                    m = map)
    
    # Generate map layer showing legislative districts
    ld.explore(name = 'Legislative Districts',
                show = False,
                column = 'LD',
                cmap = 'tab20',
                tooltip = ['LD'],
                popup = ['LD', 'County','Organizer', 'Turf', 'Total Precincts'],
                        style_kwds= {'stroke': False, 'fillOpacity': 0.45},
                        categorical = True,
                        m = map)

    # Generate map layer showing active canvassers
    addresses.explore(
        name = 'Active Canvassers',
        color = 'red',
        marker_type = 'circle_marker',
        marker_kwds = {'radius':'5'},
        show = False,
        tooltip = False,
        popup = ['myc_van_id', 'first_name', 'last_name', 'address', 'city', 'state', 'canvasses_attended'],
        m = map
        )

    # Generate map layer showing staging locations
    folium.GeoJson(
        data = staging_location['geometry'],
        name = 'Staging Locations',
        show = True,
        style_function = lambda x: {
            'fillOpacity': 0,
            'color': 'black',
            'weight':3.5,
            'fillColor':'black'},
        highlight_function= lambda x: {
            'fillOpacity': 0.5,
            'fillColor':'black'}
    ).add_to(map)

    # Generate map layer showing precincts
    precincts_map  = folium.GeoJson(
        data = precincts,
        name = 'Precincts',
        show = False,
        style_function = lambda x: {
            'fillOpacity': 0,
            'color': 'black',
            'weight':1,
            'fillColor':'black'},
        highlight_function= lambda x: {
            'fillOpacity': 0.5,
            'fillColor':'black'}
    ).add_to(map)

    precincts_map.add_child(
        folium.features.GeoJsonPopup(['VAN Precinct Name', 'LD', 'County','Organizer', 'Turf'])
        )

    # Generate map layer showing turnout target door knocking completion
    turnout_completion_map = folium.Choropleth(
        geo_data = turnout_completion,
        name= "Turnout Doors Unattempted By Precinct",
        show=False,
        fill_color = 'PuBu',
        nan_fill_color='grey',
        line_color = 'black',
        line_opacity=0.2,
        line_weight= 2,
        fill_opacity=0.45,
        highlight=True,
        data = turnout_completion,
        columns= ["van_precinct_id","percentage_not_attempted"],
        key_on= "feature.properties.van_precinct_id",
        legend_name= "Doors Unattempted By Precinct (%)").add_to(map)

    turnout_completion_map.geojson.add_child(
        folium.features.GeoJsonTooltip(['VAN Precinct Name', "staging_loc", "percentage_not_attempted"],
        aliases = ['VAN Precinct Name', "Staging Location", "Doors Unattempted (%)"])
        )

    turnout_completion_map.geojson.add_child(
        folium.features.GeoJsonPopup(['VAN Precinct Name', "staging_loc", "percentage_not_attempted", "total_doors_not_attempted"],
        aliases = ['VAN Precinct Name', "Staging Location", "Doors Unattempted (%)", 'Total Doors Unattempted'])
        )
    
    # Add search bar to make precincts searchable
    import folium.plugins as plugins
    plugins.Search(precincts_map, search_label = 'low_name', placeholder = 'search precinct (lower case)', collapsed = True).add_to(map)

    folium.LayerControl().add_to(map)

    # Generate and save map as html file
    return map.save(map_filepath)                   

def add_search_bar(map_filepath):
    """
    Adds a search bar feature to the final map to make
    it searcheable by address

    Arg
        map_filepath: str
            filepath to html map

    Return
        None
    """
    url_js = '<script src="https://unpkg.com/leaflet-geosearch@latest/dist/geosearch.umd.js"></script>'
    url_css = '<link rel="stylesheet" href="https://unpkg.com/leaflet-geosearch@latest/dist/geosearch.css"/>'

    lookup_1 = '<link rel="stylesheet" href="https://cdn.jsdelivr.net/gh/python-visualization/folium/folium/templates/leaflet.awesome.rotate.min.css"/>'
    lookup_2 = 'var map'

    # with is like your try .. finally block in this case
    with open(map_filepath, 'r') as file:
        # read a list of lines into data
        html_txt = file.readlines()

    for num, line in enumerate(html_txt, 1):
        if lookup_1 in line:
            html_txt.insert(num, '\n' + url_js + '\n' + url_css + '\n\n')
        elif lookup_2 in line:
            map_id_group = re.search('_(.*) =', line)
            map_id = map_id_group.group(1)
            add_search = f'const search = new GeoSearch.GeoSearchControl({{provider: new GeoSearch.OpenStreetMapProvider()}}); map_{map_id}.addControl(search)'
            html_txt.insert(num + 10, '\n' + add_search + '\n\n')

    # and write everything back
    with open(map_filepath, 'w') as file:
        file.writelines(html_txt)

def update_repo(map_filepath):
    """
    Updates 

    Arg:
        map_filepath: str
            File path to the map
    
    Returns
        None
    """  
    import base64
    HtmlFile = open(map_filepath, 'r', encoding='utf-8')
    with open(map_filepath, 'rb') as my_file:
        contents = base64.b64encode(my_file.read()).decode('utf-8')
    source_code = HtmlFile.read() 

    gl = gitlab.Gitlab("https://gitlab.com/", private_token= os.getenv('GITLAB_API'))
    project = gl.projects.get(39353898)

    file = project.files.get(file_path=map_filepath, ref="main")
    file.content = source_code
    file.save(branch='main', commit_message='Replace index.html')

#~~~~~~~~~~ Call Functions and Create Map ~~~~~~~~~#
@click.command()
@click.option('--precinct_shapefile_filepath', default="shapefiles/precincts_turf.shp.zip")
@click.option('--map_filepath', default="index.html")
def main(precinct_shapefile_filepath, map_filepath):
    """
    Creates
    
    """
    sheets = GoogleSheets()

    precincts = prec_shapefile_to_geodataframe(precinct_shapefile_filepath)
    organizer_assignment = get_organizer_assignment(sheets)
    precincts_assigned = generate_organizer_assignment_gdf(precincts, organizer_assignment)

    organizer, counties, ld = (group_by_col(col_name) for col_name in ['Turf', 'County', 'LD'])
    staging_location = generate_staging_location_gdf(sheets, precincts_assigned)
    turnout_completion = generate_turnout_completion_gdf(sheets, precincts_assigned)
    addresses = generate_freq_vol_gdf(sheets)
    
    to_map(map_filepath, organizer, counties, ld, addresses, staging_location, precincts, turnout_completion)
    add_search_bar(map_filepath)
    update_repo(map_filepath)