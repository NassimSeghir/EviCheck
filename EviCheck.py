#!/usr/bin/env python
# encoding: utf-8


#######################################################################################################################

# Copyright (C) 2014, Mohamed Nassim Seghir (mseghir@inf.ed.ac.uk) and David Aspinall (David.Aspinall@ed.ac.uk)
# All rights reserved.

#######################################################################################################################


from androguard.core.bytecodes import apk, dvm
from androguard.core.analysis import analysis
#from androguard.decompiler.dad import decompile
from androguard.core.bytecodes.dvm import DalvikVMFormat
from androguard.core.bytecodes.apk import APK
from androguard.core.analysis.analysis import uVMAnalysis
#from androguard.core.analysis.ganalysis import GVMAnalysis
from androguard.core.analysis.analysis import VMAnalysis
from androguard.core.analysis.analysis import *
from androguard.core.bytecodes.api_permissions import *
from EvichekFiles.TransitionSystem import *
from EvichekFiles.Monitor import *
from EvichekFiles.just_for_test import *
from guidelines.Tag_to_api_map import *
#from EvichekFiles.FromAndroWarn import *


from importlib import import_module
import importlib
import sys
import os
import base64
import pprint
import datetime
import argparse
import re
import time
import json


# will be imported from the application

# some constants
EVICHECK_EPSILON = 'EVICHECK_EPSILON'
EVICHECK_ENTRY_POINT = 'EVICHECK_ENTRY_POINT'
EVICHECK_ACTIVITY = 'EVICHECK_ACTIVITY'
EVICHECK_ACTIVITY_METHOD = 'EVICHECK_ACTIVITY_METHOD'
EVICHECK_SERVICE = 'EVICHECK_SERVICE'
EVICHECK_SERVICE_METHOD = 'EVICHECK_SERVICE_METHOD'
EVICHECK_RECEIVER_METHOD = 'EVICHECK_RECEIVER_METHOD'
EVICHECK_PACKAGE_METHOD = 'EVICHECK_PACKAGE_METHOD'
EVICHECK_ONCLICK_HANDLER = 'EVICHECK_ONCLICK_HANDLER'
EVICHECK_ONTOUCH_HANDLER = 'EVICHECK_ONTOUCH_HANDLER'
EVICHECK_DO_INBACKGROUND = 'EVICHECK_DO_INBACKGROUND'
EVICHECK_PAUSE_METHOD = 'EVICHECK_PAUSE_METHOD'
EVICHECK_ONCREATE_METHOD = 'EVICHECK_ONCREATE_METHOD'
EVICHECK_START_METHOD = 'EVICHECK_START_METHOD'
EVICHECK_RESUME_METHOD = 'EVICHECK_RESUME_METHOD'
EVICHECK_DESTROY_METHOD = 'EVICHECK_DESTROY_METHOD'




JAVA_OBJECT_CLASS = "Ljava/lang/Object"
EVICHECK_INIT_STATE = -1



# some global variables
call_graph = {}
called_by = {}
type_to_setmethods = {}
all_methods = set() 
all_classes = set()
leaf_classes = set()
root_classes = set()
tag_map = {}
class_to_methods = {}
class_inherited_from = {}
class_parent_of = {}
policy_map = {}
working_list = []
show = 0
entry_points = set()
main_activities = set()
main_activities_methods = set()
activities = set()
activities_methods = set()
services = set()
services_methods = set()
api_to_permission = {}
package_methods = set()
receivers = set()
receivers_methods = set()
providers = set()
onclick_methods = set()
ontouch_methods = set()
do_inbackground_methods = set()
on_create_methods = set()
on_start_methods = set()	
on_restart_methods = set()
on_resume_methods = set()
on_pause_methods = set()
on_destroy_methods = set()
on_stop_methods = set()

var_rename = {}
var_rename_back = {}

global_counter = 1


methodToTransSys = {} 
MonitorAutomaton = {}
MethodToAnalysis = {}

KEEP_API = 0
VM = None

# stats
verif_time = 0 
check_time = 0
pol_check_time = 0
ratio = 0
satisfied_rules = []
number_methods = 0
file_name = ""



###########################################################################################

###########################################################################################

def parseargs():
        my_arg_parser = argparse.ArgumentParser(description="Certificate generation and checking for Android apps.")
	parser = argparse.ArgumentParser(description="Certificate generation and checking for Android apps.")
	parser.add_argument("-f", "--file", help="APK File to check", type=str, required=False)
	parser.add_argument("-rf", "--res_file", help="Result file", type=str, required=False)
        parser.add_argument("-t", "--cert", help="certificate file", type=str, required=False)
	parser.add_argument("-ts", "--test_pol_spec", help="test policy for a batch spec", action ="store_true", required=False)
	parser.add_argument("-pb", "--pb_solution", help="read solution of the pseudo boolean solver sat4j", type=str, required=False)
	parser.add_argument("-so", "--soot", help="use soot as parser", action = "store_true", required=False)

	parser.add_argument("-e", "--entry", help="certificate restricted to entry points", type=str, required=False)
	parser.add_argument("-i", "--init", help="initial tag map", type=str, required=False)
	parser.add_argument("-m", "--perm", help="use permissions as initial tag map", action = "store_true", required=False)
        parser.add_argument("-l", "--list", help="display the list of methods in the APK file showing call relations", action = "store_true", required=False)
	parser.add_argument("-s", "--spec_file", help="read specification file", type=str, required=False)
	parser.add_argument("-p", "--policy", help="policy to check", type=str, required=False)
	parser.add_argument("-c", "--check", help="check certificate", action = "store_true", required=False)
	parser.add_argument("-g", "--gen", help="generate certificate", action = "store_true", required=False)	
	parser.add_argument("-gc", "--gencheck", help="generate certificate and check it then print statistics.", action = "store_true", required=False)
	parser.add_argument("-cx", "--counterexample", help="generate counterexample paths", action = "store_true", required=False)
	parser.add_argument("-k", "--keep_api", help="use api functions instead of permissions in trace monitoring", action = "store_true", required=False)
	parser.add_argument("-r", "--infer_spec", help="infer specification", type=str, required=False)
	parser.add_argument("-z3", "--z3", help="use z3 as solver", action = "store_true", required=False)
	parser.add_argument("-api", "--api", help="specs contain APIs instead of permissions", action = "store_true", required=False)
        parser.add_argument("-em", "--ext_map", help="additional (extension) API to permission map", type=str, required=False)
	args = parser.parse_args()
	return args


###########################################################################################

###########################################################################################


# must be called after set_global_vars

def extract_components_and_methods_info(apk):
	global activities_methods
	global main_activities_methods
	global services_methods
	global receivers_methods
	global on_create_methods
	global on_start_methods	
	global on_restart_methods
	global on_resume_methods
	global on_pause_methods
	global on_destroy_methods
	global on_stop_methods
	
	
 	package_name = apk.get_package()


	activities_tp = apk.get_activities()	
	for a in activities_tp:
		tmp = a.replace('.','/')
		name = 'L'+tmp
		activities.add('L'+tmp)
		if name in class_to_methods:
			#activities_methods = 			
			activities_methods = activities_methods.union(class_to_methods[name])
			

			
	for method in activities_methods:
		just_method_name =  extract_method_name(method)
		if just_method_name == "onCreate":
			on_create_methods.add(method)
		elif just_method_name == "onStart":
			on_start_methods.add(method)
		elif just_method_name == "onStop":
			on_start_methods.add(method)
		elif just_method_name == "onRestart":
			on_restart_methods.add(method)
		elif just_method_name == "onPause":
			on_pause_methods.add(method)
		elif just_method_name == "onResume":
			on_resume_methods.add(method)
		elif just_method_name == "onDestroy":
			on_destroy_methods.add(method)
			#print activities_method


	main_activities_tp = get_main_activities(apk) 
	for m in main_activities_tp:
		tmp = m.replace('.','/')
		name = 'L'+tmp
		main_activities.add('L'+tmp)
		if name in class_to_methods:
			main_activities_methods = main_activities_methods.union(class_to_methods[name])
	
	services_tp = apk.get_services()
	for s in services_tp:
		tmp = s.replace('.','/')
		name = 'L'+tmp
		services.add('L'+tmp)
		if name in class_to_methods:
			services_methods = services_methods.union(class_to_methods[name])

	
	receivers_tp = apk.get_receivers()
	for r in receivers_tp:
		tmp = r.replace('.','/')
		name = 'L'+tmp 
		receivers.add('L'+tmp)
		if name in class_to_methods:
			receivers_methods = receivers_methods.union(class_to_methods[name])

	providers_tp = apk.get_providers()
	for p in providers_tp:
		tmp = p.replace('.','/')
		providers.add('L'+tmp)

	
	add_setmethods_with_type_to_global_map('EVICHECK_ACTIVITY_METHOD', activities_methods)
	add_setmethods_with_type_to_global_map('EVICHECK_SERVICE_METHOD', services_methods)
	add_setmethods_with_type_to_global_map('EVICHECK_RECEIVER_METHOD', receivers_methods)
	add_setmethods_with_type_to_global_map('EVICHECK_ONCREATE_METHOD', on_create_methods)
	add_setmethods_with_type_to_global_map('EVICHECK_START_METHOD', on_start_methods)
	add_setmethods_with_type_to_global_map('EVICHECK_RESTART_METHOD', on_restart_methods)
	add_setmethods_with_type_to_global_map('EVICHECK_PAUSE_METHOD', on_pause_methods)
	add_setmethods_with_type_to_global_map('EVICHECK_RESUME_METHOD', on_resume_methods)
	add_setmethods_with_type_to_global_map('EVICHECK_DESTROY_METHOD', on_destroy_methods)
	add_setmethods_with_type_to_global_map('EVICHECK_STOP_METHOD', on_stop_methods)

	
###########################################################################################

###########################################################################################

def add_method_to_class(method_full_name, _class):
	if _class in class_to_methods:
		class_to_methods.add(method_full_name)
	else:
		s_tmp = set()
		s_tmp.add(method_full_name)
		class_to_methods.add(s_tmp)
			

	     
###########################################################################################
# add a method with the associated type (service, activity, etc) 
###########################################################################################

def add_method_with_type_to_global_map(method_type, method):
	if method_type in type_to_setmethods:
		type_to_setmethods[method_type].add(method)
	else:
		s_tmp = set()
		s_tmp.add(method)
		type_to_setmethods[method_type] = s_tmp
	
def add_setmethods_with_type_to_global_map(method_type, set_methods):
	if method_type in type_to_setmethods:
		type_to_setmethods[method_type] = type_to_setmethods[method_type].union(set_methods)
	else:		
		type_to_setmethods[method_type] = set_methods

###########################################################################################

###########################################################################################	

def extract_cert_key_and_val(line):
	_match = re.search(r'([^:]+)(:)(.+)', line)
	if(_match):                             
		return (_match.group(1), _match.group(3))			                                    
	else: 	
		return (None,None)


def extract_rule_head_and_tail(line):
	_match = re.search(r'([^:]+)(:\s)(.+)', line)
	if(_match):                             
		return ('and',_match.group(1), _match.group(3))			                                    
	else: 	
		_match = re.search(r'([^:]+)(:V\s)(.+)', line)
		if(_match):                             
			return ('or',_match.group(1), _match.group(3))
		else:
			return (None,None,None)

###########################################################################################

###########################################################################################

def find_negated_tags(line):
	pattern = re.compile('~[^\s]+')
	lwords = pattern.findall(line)
	return lwords

def extract_map_key(instr):
	_match = re.search(r'([^\s]+)([\s]+)(:)', instr)
	if(_match):                             
		return _match.group(1)			                                    
	else: 	
                	
		return ''

###########################################################################################

###########################################################################################


def init_api_to_permission():
	for key in DVM_PERMISSIONS_BY_ELEMENT:
		class_name = extract_class_name_from_perm_map(key)
		if class_name == '': 
			continue
		method_name = extract_method_name_from_perm_map(key)
		if method_name == '': 
			continue
		descript = extract_method_descriptor_from_perm_map(key)
		#print descript
		#print all_methods
		api_to_permission[class_name+'->'+method_name+descript] = DVM_PERMISSIONS_BY_ELEMENT[key]

	
	for method in all_methods:

		# in androguard permission map the return value is not included in the method description
		new_name = extract_method_fullname_without_return(method)
		if new_name in api_to_permission and new_name != method:
			api_to_permission[method] = api_to_permission[new_name]
			del api_to_permission[new_name]	


def copy_tag_map_and_take_return_intoaccount(source_map, dest_map, all_methods):
	for key in source_map:
		class_name = extract_class_name_from_perm_map(key)
		if class_name == '': 
			continue
		method_name = extract_method_name_from_perm_map(key)
		if method_name == '': 
			continue
		descript = extract_method_descriptor_from_perm_map(key)
		#print descript
		#print all_methods
		dest_map[class_name+'->'+method_name+descript] = source_map[key]

	
	for method in all_methods:

		# in androguard permission map the return value is not included in the method description
		new_name = extract_method_fullname_without_return(method)
		if new_name in dest_map and new_name != method:
			dest_map[method] = dest_map[new_name]
			del dest_map[new_name]	

		

def ExtendApiToPermission(api_to_permission, additional_api_perm_file):
        	
	check_file_exists(additional_api_perm_file)
	f = open(additional_api_perm_file, 'r')
        pattern = re.compile('([^:]+[\w])([\s]*)(:)([\s]*)([^\s]*)')
                
	for line in f:	
                match = re.search(pattern, line)
                if match:
                        if len(match.group(5)) > 0: 
                                api_to_permission[match.group(1)] = match.group(5)
                else:
                        sys.exit('bad format of the API-to-permission map')
###########################################################################################


def init_api_to_permission_for_soot():

	for key in DVM_PERMISSIONS_BY_ELEMENT:
		
		
		class_name = extract_class_name_from_perm_map(key)
		if class_name == '': 
			continue
		method_name = extract_method_name_from_perm_map(key)
		if method_name == '': 
			continue
		descript = extract_method_descriptor_from_perm_map(key)
		descript = descript.replace(" ","")
		#print descript
		#print all_methods
		api_to_permission[class_name+'->'+method_name+descript] = DVM_PERMISSIONS_BY_ELEMENT[key]
		#if key == 'Landroid/app/Activity;-setContentView-(I)':
		#	print class_name+'->'+method_name+descript
		#	sys.exit(0)
		

	for method in all_methods:

		# in androguard permission map the return value is not included in the method description
		new_name = extract_method_fullname_without_return(method)
		if new_name in api_to_permission and new_name != method:
			api_to_permission[method] = api_to_permission[new_name]
			del api_to_permission[new_name]

###########################################################################################



def extract_class_name_from_perm_map(instr):
	_match = re.search(r'((\W|\w)+)(;-)', instr)
	if(_match):                             
		return _match.group(1)			                                    
	else: 	
                	
		return ''


def extract_method_name_from_perm_map(instr):
	_match = re.search(r'(;-)((\W|\w)+)(-\()', instr)
	if(_match):                             
		return _match.group(2)			                                    
	else: 	
                	
		return ''

def extract_method_fullname_without_return(method_name):
	_match = re.search(r'((\W|\w)+\))', method_name)
	if(_match):                             
		return _match.group(1)			                                    
	else: 	
                	
		return ''



def extract_method_descriptor_from_perm_map(instr):
	_match = re.search(r'(\((\W|\w)*\))', instr)
	if(_match):                             
		return _match.group(1)			                                    
	else: 	
                	
		return ''


def extract_class_name(instr):
	_match = re.search(r'((\W|\w)+)(;->)', instr)
	if(_match):                             
		return _match.group(1)			                                    
	else: 	
                	
		return ''


def extract_method_descriptor(instr):
	_match = re.search(r'(\((\W|\w)+)', instr)
	if(_match):
		descr = _match.group(1)
 
		if descr[len(descr)-1] == ';':
			descr = descr[0:len(descr)-1]

		return descr			                                    
	else: 	
                	
		return ''




def extract_method_name(instr):
	_match = re.search(r'(->)((\W|\w)+)(\()', instr)
	if(_match):                             
		return _match.group(2)			                                    
	else: 	
                	
		return ''

def extract_method_name_form_classtomethods(instr):
	_match = re.search(r'(->)((\W|\w)+)', instr)
	if(_match):                             
		return _match.group(1)			                                    
	else: 	
                	
		return ''




def extract_method_name_form_classtomethods(method_set):
	res = set()
	
	for method in method_set:		
		_match = re.search(r'(->)((\W|\w)+)', method)
		if(_match):  
			res.add(_match.group(1))
	return res




def extract_method_fullname(instr):
	_match = re.search(r'(\w+)(;))', instr)
	if(_match):                             
		return _match.group(2)			                                    
	else: 	               	
		return ''




###########################################################################################

###########################################################################################

def get_main_activities(apk_file):
	"""
            Return the name of the main activity

            :rtype: string
        """
        x = set()
        y = set()

        for i in apk_file.xml:
            for item in apk_file.xml[i].getElementsByTagName("activity") :
                for sitem in item.getElementsByTagName( "action" ) :
                    val = sitem.getAttribute( "android:name" )
                    if val == "android.intent.action.MAIN" :
                        x.add( item.getAttribute( "android:name" ) )
                   
                for sitem in item.getElementsByTagName( "category" ) :
                    val = sitem.getAttribute( "android:name" )
                    if val == "android.intent.category.LAUNCHER" :
                        y.add( item.getAttribute( "android:name" ) )
                
        z = x.intersection(y)      
        res = set()
        for a in z:
            res.add(apk_file.format_value(a))        
        
        return res

###########################################################################################

###########################################################################################


def check_file_exists(myfile):        
	if not os.path.isfile(myfile):
		print '\nCan\'t find file: '+myfile+'\n'
		sys.exit(0)

def generate_default_init_map(method_set):
	res = {}
	count = 0;
	for method in method_set:
		set_tmp = set()
                #if count < 50:
		set_tmp.add('TAG_'+method)
                tag_map[method] = set_tmp




                
def generate_default_init_map_from_previous_version(method_set,file_name):	
	tag_map.clear()
	for method in method_set:
                tag_map[method] = set()
	check_file_exists(file_name)
	f = open(file_name, 'r')
        pattern = re.compile('[^\s]+')
	for line in f:	
                key = ''
                tag_set = set()	
		lwords = pattern.findall(line)			
		for word in lwords:
			if(word[len(word)-1] == ':'):
				key = word[0:len(word)-1]

			else:
				tag_set.add(word)
		if key == '':
			sys.exit('Tag map format invalid')

		tag_map[key] = tag_set


def generate_default_init_map_from_file(method_set,file_name):	
	tag_map.clear()
	for method in method_set:
                tag_map[method] = set()
	check_file_exists(file_name)
	f = open(file_name, 'r')
        pattern = re.compile('[^\s]+')
	for line in f:	
                key = extract_map_key(line)
		if key == '':
			sys.exit('Tag map format invalid')
                tag_set = set()	
		lwords = pattern.findall(line)		
		for word in lwords:
			if(word != key and word != ':'):				
				tag_set.add(word)		
		tag_map[key] = tag_set	





def generate_init_map_from_permissions(method_set):
	#init_api_to_permission()
	
	#for method in all_methods:

		# in androguard permission map the return value is not included in the method description
	#	new_name = extract_method_fullname_without_return(method)
	#	if new_name in api_to_permission and new_name != method:
	#		api_to_permission[method] = api_to_permission[new_name]
	#		del api_to_permission[new_name]


	for key in method_set:
		if key in api_to_permission.keys():
			settmp = set()
			settmp.add(api_to_permission[key])
			tag_map[key] = settmp 
		else:
			tag_map[key] = set()





###########################################################################################
# copy the content corresponding to each entry in all_entries from map_source to map_dest
# if an entry is not in map_source, the empty set is associated with it in map_dest
###########################################################################################




def copy_content_for_entries(all_entries, map_source, map_dest):
	
	for key in all_entries:
		if key in map_source.keys():
			settmp = set()
			settmp.add(map_source[key])
			map_dest[key] = settmp 
		else:
			map_dest[key] = set()



def generate_init_map_from_permissions2(method_set):
	init_api_to_permission()
	for key in method_set:
		if key in api_to_permission.keys():
			settmp = set()
			settmp.add(api_to_permission[key]+'_PERM_'+key)
			tag_map[key] = settmp 
		else:
			tag_map[key] = set()



###########################################################################################

###########################################################################################

def propagate_methods_using_inheritance(class_name):
	methods = set()
	methods_to_return =  set()
	if class_name in root_classes:

		if class_name in class_to_methods:
			methods = class_to_methods[class_name]

		for met in methods:
			m_id = extract_method_name_form_classtomethods(met)
			methods_to_return.add(m_id)
		
		return methods_to_return

	else:
		parent_class = class_parent_of(class_name)
		parent_methods = set()
		current_methods = set()
		parent_methods = propagate_methods_using_inheritance(parent_class)

		if class_name in class_to_methods:
			current_methods = class_to_methods[class_name]

		current_methods = extract_method_name_form_classtomethods(current_methods)
		not_overwritten_methods = []
		not_overwritten_methods = parent_methods.difference(current_methods)

		for method in not_overwritten_methods:
			full_name = class_name + '->'+method
			add_method_to_class(full_name, class_name)
		method_to_return = current_methods.union(not_overwritten_methods)
		return methods_to_return
		
	

###########################################################################################

###########################################################################################


# populate the globale variables: call greaph, method list, etc.

def set_global_vars3(apk_file_name):
	
	_a = apk.APK(apk_file_name)
        
	_vm = dvm.DalvikVMFormat(_a.get_dex())
	my_vm = VMAnalysis(_vm)
	for ms in _vm.get_methods():
		#ms.pretty_show()
		m = my_vm.get_method(ms)
		if ms.get_code() == None:
			continue
		print ms.get_class_name(), ms.get_name(), ms.get_descriptor()
		idx = 0		
		ExtractSpecAsRegExpFromCFG(m.get_basic_blocks().get())
		

def set_global_vars4(apk_file_name):
	
	_a = apk.APK(apk_file_name)
        
	_vm = dvm.DalvikVMFormat(_a.get_dex())
	my_vm = VMAnalysis(_vm)
        
	for ms in _vm.get_methods():
		#ms.pretty_show()
		m = my_vm.get_method(ms)
		if ms.get_code() == None:
			continue
		#print ms.get_class_name(), ms.get_name(), ms.get_descriptor()
		idx = 0		
		class_name = ms.get_class_name()
		if class_name[len(class_name)-1] == ';':
			class_name = class_name[0:len(class_name)-1]
		method_name = ms.get_name()
		describ = ms.get_descriptor()
		method_full_name = class_name +'->'+method_name + describ
		#ExtractSpecAsRegExpFromCFG(m.get_basic_blocks().get())
		#if count < 3:
		ExtractAPITransitionSystem(m.get_basic_blocks().get(), method_full_name)
			#print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>", count
			
	
		

def set_global_vars2(apk_file_name):
	
	_a = apk.APK(apk_file_name)
        
	_vm = dvm.DalvikVMFormat(_a.get_dex())
	my_vm = VMAnalysis(_vm)
	for ms in _vm.get_classes():
		print '==============================================================='
		print ms.get_name()
		print ms.get_superclassname()
		print '==============================================================='
	
	for ms in _vm.get_methods():
		ms.pretty_show()
	return
	for ms in _vm.get_methods():
		#ms.pretty_show()
		m = my_vm.get_method(ms)
		if ms.get_code() == None:
			continue
		print ms.get_class_name(), ms.get_name(), ms.get_descriptor()
		idx = 0
		
		#ExtractSpecAsRegExpFromCFG(m.get_basic_blocks().get())
		
		for i in m.get_basic_blocks().get():
			print "\t %s %x %x" % (i.name, i.start, i.end), '[ NEXT = ', ', '.join( "%x-%x-%s" % (j[0], j[1], j[2].get_name()) for j in i.get_next() ), ']', '[ PREV = ', ', '.join( j[2].get_name() for j in i.get_prev() ), ']'

			for ins in i.get_instructions():
				print "\t\t %x" % idx, ins.get_name(), ins.get_output()
				idx += ins.get_length()

			print ""
		if ms.get_name()  == 'feedbackTypeToString':
			show = 1
		ExtractSpecAsRegExpFromCFG(m.get_basic_blocks().get())
		if ms.get_name()  == 'feedbackTypeToString':
			return
		print '\n===========================================================================================\n'
	return	
	#_vmx = uVMAnalysis(_vm)
	#_vm.show_Permissions()
#	return
	
	
	
	#for perm in perms:
		#perm.show()
	
	

	for current_method in _vm.get_methods():              
              c_name = current_method.get_class_name()
              method_id = c_name[0:len(c_name)-1]+'->'+current_method.get_name()
              called = set()
	      for ins in current_method.get_instructions(): 
                        if ins.get_name() == "invoke-virtual" or ins.get_name() == "invoke-direct":
                            _str = ins.get_translated_kind()
                            m_name = extract_method_name(_str)
                            m_class = extract_class_name(_str)                                                        
                            if(m_name != '' and m_class != ''):
                             m_name = m_class +'->'+m_name;			     
                             called.add(m_name)			                                    
			    else: 
                             #print 'not found in ', _str
                             continue
                            
                            if m_name in called_by:
                              called_by[m_name].add(method_id)
                            else: 
                              set_tmp = set()
                              set_tmp.add(method_id)
                              called_by[m_name] = set_tmp
                            
                            if method_id in call_graph:
                              call_graph[method_id].add(m_name)
			    else:
                              set_tmp = set()
			      set_tmp.add(m_name)                               
                              call_graph[method_id] = set_tmp

                            all_methods.add(m_name)
			    all_methods.add(method_id)



###########################################################################################

###########################################################################################

def ExtractAPITransitionSystem(list_basic_blocks, method_full_name):
	global methodToTransSys
	#locToRegExp = {}
	#locToSucc = {}
	#locToPrev = {}
        #transToLabels = {} 
	#initLoc = 0
	#setFinalLocs = set()
	#basicBlockNames = []
	#finalLocsMap = {}

	
	transSys = TransitionSystem()
	
	for i in list_basic_blocks:
		if len(i.get_prev()) == 0 and i.start != 0 :
			continue
		#basicBlockNames.append(i.name)
		
		if (len(i.get_next()) == 0) and (len(i.get_prev()) == 0) and (i.start != 0):
			continue

		# only collect method invokations
		list_tmp = []
		for ins in i.get_instructions():
			if ins.get_name() == "invoke-virtual" or ins.get_name() == "invoke-direct" or ins.get_name() == "invoke-static" or ins.get_name() == "invoke-virtual/range":
				_str = ins.get_translated_kind()
				
				method_name = extract_method_name(_str)
				class_name = extract_class_name(_str) 
				desc = extract_method_descriptor(_str)
				
				if(method_name != '' and class_name != ''):
					#print api_to_permission
					#print KEEP_API
					#sys.exit("") 
					method_name = class_name +'->'+method_name + desc;

					# remove the V at the end
					method_name_without_return = extract_method_fullname_without_return(method_name)
					#if method_name == 'Landroid/media/MediaRecorder->setAudioSource(I)V':
						#print method_name
						#sys.exit("")
					if (KEEP_API == 0):
						if (method_name_without_return in api_to_permission):
							list_tmp.append(api_to_permission[method_name_without_return])
						#else:
						#	list_tmp.append(EVICHECK_EPSILON)

					else:
						list_tmp.append(method_name)	                                    
				else:                              
					continue
		if len(list_tmp) == 0:
			list_tmp.append(EVICHECK_EPSILON)		
	

		# adding successors
		if len(i.get_next()) == 0:
			#setFinalLocs.add(i.name)
			#finalLocsMap[i.name] = '('+' ; '.join(list_tmp) + ')'
			set_dummy = set()
			set_dummy.add(transSys.finalLoc)
			transSys.AddSucc(i.name,set_dummy)
			transSys.AddTrans(i.name, transSys.finalLoc, list_tmp)
			transSys.LocToPreced[transSys.finalLoc].add(i.name)
		else:		
			set_next_tmp = set()
			for b in i.get_next():
				set_next_tmp.add(b[2].get_name())
				transSys.AddTrans(i.name, b[2].get_name(), list_tmp)
			#transToLabels[(i.name, b[2].get_name())] = '('+' ; '.join(list_tmp) + ')'
		#locToSucc[i.name] = set_next_tmp
			transSys.AddSucc(i.name,set_next_tmp)	
		
                
		# adding predecessors		
		if len(i.get_prev()) == 0 and i.start == 0 :                
			transSys.SetInitLoc(i.name)
		else:
			set_prev_tmp = set()
			for b in i.get_prev():		
				set_prev_tmp.add(b[2].get_name())
			#locToPrev[i.name] = set_prev_tmp
			transSys.AddPreced(i.name,set_prev_tmp)
	
	methodToTransSys[method_full_name] = transSys
	#print method_name
	#methodToTransSys[method_name].Print()
	#transSys.Print()
###########################################################################################

###########################################################################################




# extrcat regular expressions from the CFG

def ExtractSpecAsRegExpFromCFG(list_basic_blocks):
	
	locToRegExp = {}
	locToSucc = {}
	locToPrev = {}
        transToLabels = {} 
	initLoc = 0
	setFinalLocs = set()
	basicBlockNames = []
	finalLocsMap = {}

	if show == 1: 
		return
	#assert(len(basicBlockNames) != 0)	
	#for i in list_basic_blocks:
	#	print '\n!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n'
	
	for i in list_basic_blocks:
		if len(i.get_prev()) == 0 and i.start != 0 :
			continue
		basicBlockNames.append(i.name)
		#print '\n!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!-------------------\n'
		# just ignore non-connected blocks
		if (len(i.get_next()) == 0) and (len(i.get_prev()) == 0) and (i.start != 0):
			continue

		# only collect method invokations
		list_tmp = []
		for ins in i.get_instructions():
			if ins.get_name() == "invoke-virtual" or ins.get_name() == "invoke-direct" or ins.get_name() == "invoke-static" or ins.get_name() == "invoke-virtual/range":
				_str = ins.get_translated_kind()
				method_name = extract_method_name(_str)
				class_name = extract_class_name(_str)                                                        
				if(method_name != '' and class_name != ''):
					method_name = class_name +'->'+method_name;			     
					list_tmp.append(method_name)	                                    
				else:                              
					continue
		if len(list_tmp) == 0:
			list_tmp.append(EVICHECK_EPSILON)		
		locToRegExp[i.name] = list_tmp

		# adding successors
		if len(i.get_next()) == 0:
			setFinalLocs.add(i.name)
			finalLocsMap[i.name] = '('+' ; '.join(list_tmp) + ')'
		else:		
			set_next_tmp = set()
			for b in i.get_next():
				set_next_tmp.add(b[2].get_name())
				transToLabels[(i.name, b[2].get_name())] = '('+' ; '.join(list_tmp) + ')'
			locToSucc[i.name] = set_next_tmp
			
		
                
		# adding predecessors		
		if len(i.get_prev()) == 0 and i.start == 0 :                
			initLoc = i.name
		else:
			set_prev_tmp = set()
			for b in i.get_prev():		
				set_prev_tmp.add(b[2].get_name())
			locToPrev[i.name] = set_prev_tmp

	#or i in listBasicBlock:
		#rint '\n!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n'
	count = 0
	for block_name in basicBlockNames:
		#print '\n!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n'
		
		if block_name != initLoc and block_name not in setFinalLocs:
			#rint '\n!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n'
			#print 'CURRENT BLOCK:', block_name
			#print 'FINAL LOCKS:', setFinalLocs
			
			prev = locToPrev[block_name]
			succ = locToSucc[block_name]
			transToDelete = set()
			deleteInPrev = set()
			deleteInSucc = set()

			#print 'TRANS BEFORE: ', transToLabels
			for b_prev in prev:
				for b_succ in succ:
					if show == 1:
						++count
					str_tmp = ''

					if (block_name,block_name) in transToLabels:
						str_tmp = transToLabels[(block_name,block_name)]						
						str_tmp = transToLabels[(b_prev,block_name)] + '; ('+str_tmp +')* ; '+ transToLabels[(block_name, b_succ)]
					else:
						str_tmp = transToLabels[(b_prev,block_name)] + ' ; '+ transToLabels[(block_name, b_succ)]

					if(b_prev,b_succ) in transToLabels:
						transToLabels[(b_prev,b_succ)] = '((' + transToLabels[(b_prev,b_succ)] + ') | (' + str_tmp + '))'
					else:
						transToLabels[(b_prev,b_succ)] = transToLabels[(b_prev,b_succ)] = str_tmp
			

					if (block_name,block_name) in transToLabels:
						#del transToLabels[(block_name,block_name)]
						transToDelete.add((block_name,block_name))

					#del transToLabels[(block_name,b_succ)]
					transToDelete.add((block_name,b_succ))
					#locToPrev[b_succ].remove(block_name)
					deleteInPrev.add(b_succ)
					locToPrev[b_succ].add(b_prev)
					locToSucc[b_prev].add(b_succ)

				#del transToLabels[(b_prev,block_name)]
				transToDelete.add((b_prev,block_name))
				#locToSucc[b_prev].remove(block_name)
				deleteInSucc.add(b_prev)
				#print '\n\nTrans after: ', transToLabels
				
		# update trasitions		
			for (p1,p2) in transToDelete:
				del transToLabels[(p1,p2)]
			for b_prev in deleteInPrev:
				locToPrev[b_prev].remove(block_name)
			for b_succ in deleteInSucc:
				locToSucc[b_succ].remove(block_name)

			#print 'TRANS AFTER: ', transToLabels
	if show == 1: 
		return
	# add final sequences associated with final locations			
	for (p1,p2) in transToLabels:
		transToLabels[(p1,p2)] = transToLabels[(p1,p2)] + ' ; '+finalLocsMap[p2] 


	print '\n\nTrans Final: ', transToLabels

	assert len(setFinalLocs) > 0
	assert initLoc != 0
	#print '\nINIT:', initLoc


	#for key,val in transToLabels.iteritems() :
	#	print 'Trans:', key
	#	print val
	#	print '\n----------------------------------------------\n'
	
#	for key,val in locToRegExp.iteritems() :
#		print 'key:',key		
#		print val
#		print '\n----------------------------------------------\n'
		
	


###########################################################################################

###########################################################################################


def set_global_vars_previous(apk_file_name):
	_apk = apk.APK(apk_file_name)  			
	#return
	_vm = dvm.DalvikVMFormat(_apk.get_dex())
	#my_vm = VMAnalysis(_vm)
	#show_Permissions(my_vm)
	#return
	#for current_method in _vm.get_methods(): 
	#	current_method.pretty_show()
	#return	
	
	for current_method in _vm.get_methods():              
              c_name = current_method.get_class_name()
	      c_name = c_name[0:len(c_name)-1]
              method_id = c_name+'->'+current_method.get_name()

	      # check is the method is an event handler
	      if(current_method.get_name() == "onClick"):
		      onclick_methods.add(method_id)
	      if(current_method.get_name() == "onTouch"):
		      ontouch_methods.add(method_id)		      

	      
	      if c_name in class_to_methods:
		      class_to_methods[c_name].add(method_id)
	      else:
		      set_tmp = set()
		      set_tmp.add(method_id)
		      class_to_methods[c_name] = set_tmp
		      
	      called = set()
	      for ins in current_method.get_instructions(): 
                        if ins.get_name() == "invoke-virtual" or ins.get_name() == "invoke-direct" or ins.get_name() == "invoke-static" or ins.get_name() == "invoke-virtual/range":
                            _str = ins.get_translated_kind()
                            m_name = extract_method_name(_str)
                            m_class = extract_class_name(_str)                                                        
                            if(m_name != '' and m_class != ''):
				    m_name = m_class +'->'+m_name;			     
				    called.add(m_name)	
				    
				    if m_class in class_to_methods:
					    class_to_methods[m_class].add(m_name)
				    else:
					    set_tmp = set()
					    set_tmp.add(m_name)
					    class_to_methods[m_class] = set_tmp
			    else: 
                             #print 'not found in ', _str
				    continue
                            
                            if m_name in called_by:
                              called_by[m_name].add(method_id)
                            else: 
                              set_tmp = set()
                              set_tmp.add(method_id)
                              called_by[m_name] = set_tmp
                            
                            if method_id in call_graph:
                              call_graph[method_id].add(m_name)
			    else:
                              set_tmp = set()
			      set_tmp.add(m_name)                               
                              call_graph[method_id] = set_tmp

                            all_methods.add(m_name)

			    all_methods.add(method_id)

	# entry points are not called by any other methods
	for method in all_methods:
		if method not in called_by and (method != 'LdummyMainClass->dummyMainMethod()V'):
			entry_points.add(method)


	for _class in _vm.get_classes():
		base_class = _class.get_superclassname()
	
		# obvious
		if (base_class == JAVA_OBJECT_CLASS):
			continue
		
		inherited_class = _class.get_name()
		
		# get rid of the comma at the end
		base_class = base_class[0:len(base_class)-1]
		inherited_class = inherited_class[0:len(inherited_class)-1]
		all_classes.add(inherited_class)
	
		class_parent_of[inherited_class] = base_class
		
		if base_class in class_inherited_from :
			class_inherited_from[base_class].add(inherited_class)
		else:
			set_tmp = set()
			set_tmp.add(inherited_class)
			class_inherited_from[base_class] = set_tmp
	non_leaf = set()
	for _class in all_classes:
		if _class not in class_inherited_from:
			leaf_classes.add(_class)
		if _class not in class_parent_of:
			root_classes.add(_class)
				
	#print '===================================================='
	#print class_parent_of
	#print '===================================================='			
	#print class_inherited_from
	#for _class in 
	#print class_inherited_from
	#print '\n\n\n\n\n\n\n'
	#print leaf_classes
	#print '\n\n\n\n\n\n\n'
	#print non_leaf
	#add_methods_based_on_inheritence()
	return

	
	



	methods = set()
	for method in all_methods:		
		if method not in called_by:
			methods.add(method)
			
	for method in methods:
		if 'EVICHECK_MAIN' in call_graph:
			call_graph['EVICHECK_MAIN'].add(method)
		else:
			set_tmp = set()
			set_tmp.add(method)
			call_graph['EVICHECK_MAIN'] = set_tmp


		if method in called_by:			
			called_by[method].add('EVICHECK_MAIN')
		else:			
			set_tmp = set()
			set_tmp.add('EVICHECK_MAIN')
			called_by[method] = set_tmp
		


###########################################################################################

###########################################################################################


def set_global_vars(apk_file_name):
	global VM
	_apk = apk.APK(apk_file_name)  			
	#return
	VM = dvm.DalvikVMFormat(_apk.get_dex())
	#my_vm = VMAnalysis(_vm)
	#show_Permissions(my_vm)
	#return
	#for current_method in _vm.get_methods(): 
	#	current_method.pretty_show()
	#return	
	
	for current_method in VM.get_methods():              
              c_name = current_method.get_class_name()
	      
	      c_name = c_name[0:len(c_name)-1]
	
	      
              method_id = c_name+'->'+current_method.get_name()
	      descriptor = current_method.get_descriptor()
	      
	      if descriptor[len(descriptor)-1] == ';':
		      descriptor = descriptor[0:len(descriptor)-1]
	      method_id = method_id + descriptor
	      
	      
	      # check is the method is an event handler
	      if(current_method.get_name() == "onClick"):
		      onclick_methods.add(method_id)
		      add_method_with_type_to_global_map('EVICHECK_ONCLICK_HANDLER', method_id)
	      if(current_method.get_name() == "onTouch"):
		      ontouch_methods.add(method_id)		      
		      add_method_with_type_to_global_map('EVICHECK_ONTOUCH_HANDLER', method_id)	      
	      if(current_method.get_name() == "doInBackground"):
		      do_inbackground_methods.add(method_id)		      
		      add_method_with_type_to_global_map('EVICHECK_DO_INBACKGROUND', method_id)

	      if c_name in class_to_methods:
		      class_to_methods[c_name].add(method_id)
	      else:
		      set_tmp = set()
		      set_tmp.add(method_id)
		      class_to_methods[c_name] = set_tmp
		      
	      called = set()
	      for ins in current_method.get_instructions(): 
                        if ins.get_name() == "invoke-virtual" or ins.get_name() == "invoke-direct" or ins.get_name() == "invoke-static" or ins.get_name() == "invoke-virtual/range":
                            _str = ins.get_translated_kind()
			
			    
                            m_name = extract_method_name(_str)
                            m_class = extract_class_name(_str)
			    m_desc = extract_method_descriptor(_str)
			   
                            if(m_name != '' and m_class != ''):
				    m_name = m_class +'->'+m_name + m_desc;			     
				    called.add(m_name)	
				    
				    if m_class in class_to_methods:
					    class_to_methods[m_class].add(m_name)
				    else:
					    set_tmp = set()
					    set_tmp.add(m_name)
					    class_to_methods[m_class] = set_tmp
			    else: 
                             #print 'not found in ', _str
				    continue
                            
                            if m_name in called_by:
                              called_by[m_name].add(method_id)
                            else: 
                              set_tmp = set()
                              set_tmp.add(method_id)
                              called_by[m_name] = set_tmp
                            
                            if method_id in call_graph:
                              call_graph[method_id].add(m_name)
			    else:
                              set_tmp = set()
			      set_tmp.add(m_name)                               
                              call_graph[method_id] = set_tmp

                            all_methods.add(m_name)

			    all_methods.add(method_id)

	# entry points are not called by any other methods
	for method in all_methods:
		if method not in called_by:
			entry_points.add(method)


	for _class in VM.get_classes():
		base_class = _class.get_superclassname()
	
		# obvious
		if (base_class == JAVA_OBJECT_CLASS):
			continue
		
		inherited_class = _class.get_name()
		
		# get rid of the comma at the end
		base_class = base_class[0:len(base_class)-1]
		inherited_class = inherited_class[0:len(inherited_class)-1]
		all_classes.add(inherited_class)
	
		class_parent_of[inherited_class] = base_class
		
		if base_class in class_inherited_from :
			class_inherited_from[base_class].add(inherited_class)
		else:
			set_tmp = set()
			set_tmp.add(inherited_class)
			class_inherited_from[base_class] = set_tmp
	non_leaf = set()
	for _class in all_classes:
		if _class not in class_inherited_from:
			leaf_classes.add(_class)
		if _class not in class_parent_of:
			root_classes.add(_class)
				
	#print '===================================================='
	#print class_parent_of
	#print '===================================================='			
	#print class_inherited_from
	#for _class in 
	#print class_inherited_from
	#print '\n\n\n\n\n\n\n'
	#print leaf_classes
	#print '\n\n\n\n\n\n\n'
	#print non_leaf
	#add_methods_based_on_inheritence()
	return

	
	



	methods = set()
	for method in all_methods:		
		if method not in called_by:
			methods.add(method)
			
	for method in methods:
		if 'EVICHECK_MAIN' in call_graph:
			call_graph['EVICHECK_MAIN'].add(method)
		else:
			set_tmp = set()
			set_tmp.add(method)
			call_graph['EVICHECK_MAIN'] = set_tmp


		if method in called_by:			
			called_by[method].add('EVICHECK_MAIN')
		else:			
			set_tmp = set()
			set_tmp.add('EVICHECK_MAIN')
			called_by[method] = set_tmp
		




###########################################################################################

###########################################################################################

def gen_certificate():		
        for method in tag_map.iterkeys():		
		if method not in working_list:
		   working_list.append(method)
	
	while len(working_list) > 0:
          method = working_list[0]
          working_list.pop(0)          
          callees = []
	  if method in call_graph:
             callees = call_graph[method]
	  
          set_tmp = tag_map.get(method)
	  prev_size = len(set_tmp)
          
	  for callee in callees:          
              set_tmp = set_tmp.union(tag_map[callee])   	      
	  
          
    
	  if(len(set_tmp) != prev_size and (method in called_by)):
            if(len(set_tmp) < prev_size):
              sys.exit('impossible !!!')
              
                    
            for caller in called_by[method]:
               if caller not in working_list:
                  working_list.append(caller) 

          tag_map[method] = set_tmp
	  

def check_certificate():
        tag_map0 = tag_map	

        
        for caller, callees in call_graph.iteritems():
                 
                assert caller not in api_to_permission
                
                if caller not in tag_map:
                        print '\n\nInvalid certificate! Entry: ' + caller + ' is not present\n\n'
                        return

                current_entry_tags = tag_map[caller]

                tag_set = set()
                
                for callee in callees:                        
                        if callee not in tag_map:
                                print '\n\nInvalid certificate! Entry: ' + callee + ' is not present\n\n'
                                return
                                
                        if callee in api_to_permission:
                                # res is one element (permission) and not a set 
                                res = api_to_permission[callee]													
                                if res not in tag_map[callee]:
                                        print '\n\nInvalid certificate! Problem located in method: ' + callee + '\n\n'	
                                        return
                        tag_set = tag_set.union(tag_map[callee])
                                                
                
                res = current_entry_tags.symmetric_difference(tag_set)	
                if len(res) > 0:                                
                        print '\n\nInvalid certificate! Problem located in method: ' + caller + '\n\n'                
                        return
        print '\n\nCertificate valid!\n\n'
        




def check_certificate_previous():
        tag_map0 = tag_map	
	for key in tag_map.iterkeys():         
		tag_set = tag_map.get(key)
		#tag_set2 = tag_map0.get(key)
		tag_set2 = set()
                #print "----------------------------------------"		

		if key in call_graph and key not in api_to_permission:
		
			callees = call_graph[key]
			for callee in callees:
				if callee not in tag_map:
					print '\n\nInvalid certificate! Entry: ' + callee + ' is not present\n\n'
					return

				if callee in api_to_permission:
					# res is one element (permission) and not a set 
					res = api_to_permission[callee]													
					if res not in tag_map[callee]:
						print '\n\nInvalid certificate! Problem located in method: ' + callee + '\n\n'	
						return

				#print 'tag_map_callee', tag_map[callee]
				tag_set2 = tag_set2.union(tag_map[callee])
			res = tag_set.symmetric_difference(tag_set2)	
			if len(res) > 0:        
				#print res
				#print tag_set
				#print tag_set2
			
				print '\n\nInvalid certificate! Problem located in method: ' + key + '\n\n'				
				return
		
		

		
	print '\n\nCertificate valid!\n\n'	 



def check_certificate2():
	
	#_apk = apk.APK(file_name)  			
	#return
	#_vm = dvm.DalvikVMFormat(_apk.get_dex())

	
	      #if caller_method == 'Lcom/flurry/android/FlurryAgent->a':
		      #print current_method.get_descriptor()
	

	for current_method in VM.get_methods():              
              c_name = current_method.get_class_name()
	      c_name = c_name[0:len(c_name)-1]
              caller_method = c_name+'->'+current_method.get_name()
	      #if caller_method == 'Lcom/flurry/android/FlurryAgent->a':
	#	      my_list  = current_method.get_instructions()
	#	      print my_list
	#	      return
	      if caller_method not in tag_map:
		      continue
	      caller_tags = set()
	      caller_tags = tag_map[caller_method]
	      callees_tags = set()
	    #  print '--------------------------------------------'
	     # print '********************************************'
	     # print caller_method
	     # if caller_method in call_graph:
	#	      print call_graph[caller_method]
	 #     print '********************************************'

	      for ins in current_method.get_instructions():
		      if ins.get_name() == "invoke-virtual" or ins.get_name() == "invoke-direct" or ins.get_name() == "invoke-static" or ins.get_name() == "invoke-virtual/range":
                            _str = ins.get_translated_kind()
                            m_name = extract_method_name(_str)
                            m_class = extract_class_name(_str)                                                        
                            if(m_name != '' and m_class != ''):
				    m_name = m_class +'->'+m_name
				    if m_name not in tag_map:
					    print '\n\nInvalid certificate! Entry: ' + m_name + ' is not present\n\n'
					    return
				    callees_tags = callees_tags.union(tag_map[m_name])
				    #print m_name, tag_map[m_name]
			    #if caller_method == 'Lcom/flurry/android/FlurryAgent->a':
			#	    print ins.get_translated_kind()

	      res = caller_tags.symmetric_difference(callees_tags)	
	      if len(res) > 0:        
		      #print res
		      #print callees_tags
		      #print caller_tags
			
		      print '\n\nInvalid certificate! Problem located in method: ' + caller_method + '\n\n'
		      return
				
	print '\n\nCertificate valid\n\n'
	return

        tag_map0 = tag_map	
	for key in tag_map.iterkeys():         
		tag_set = tag_map.get(key)
		tag_set2 = tag_map0.get(key)
		if key in call_graph:
			callees = call_graph[key]
			for callee in callees:
				if callee not in tag_map:
					print '\n\nInvalid certificate! Entry: ' + callee + ' is not present\n\n'
					return
				tag_set2 = tag_set2.union(tag_map[callee])
				res = tag_set.symmetric_difference(tag_set2)	
				if len(res) > 0:           
					print '\n\nInvalid certificate! Problem located in method: ' + key + '\n\n'
					return
				
	print '\n\nCertificate valid\n\n'	 


def check_policy2():
	for key in policy_map.iterkeys():
		if key not in tag_map:
			 continue
		
		set_tmp = policy_map[key]
		set_tmp2 = tag_map[key]
		
		for method in set_tmp:
			if method not in set_tmp2:
				print 'Invalid policy. Problem located in method: ', key
				return

	print 'Policy is valid'	

	
def print_certificate2():
	for key in tag_map.iterkeys():
		line = key + ': '                  
		tag_set = tag_map.get(key)
		for tag in tag_set:            
			line = line + ' '+tag 
			 
		print line	 

def print_certificate(file_name):	
	f = open(file_name, 'w')
	if f is None:
		sys.exit('Can\'t open file '+file_name)
	for key in tag_map.iterkeys():
		line = key + ': '                  
		tag_set = tag_map.get(key)
		for tag in tag_set:            
			line = line + ' '+tag 
			 
		f.write(line+'\n')
	f.close()
	 
def print_certificate_for_entry_points(file_name):	
	f = open(file_name, 'w')
	if f is None:
		sys.exit('Can\'t open file '+file_name)
	for key in entry_points:
		line = key + ': '                  
		tag_set = tag_map.get(key)
		for tag in tag_set:            
			line = line + ' '+tag 
			 
		f.write(line+'\n')
	f.close()



def pretty_print_certificate():
	for key in tag_map.iterkeys():
         print '==============================================='
         print 'Method: ', key
	 tag_set = tag_map.get(key)
	 for tag in tag_set:            
          print '--> ',tag
	 print '==============================================='

def print_call_graph(): 
	for key in call_graph.iterkeys():
         #if key=='M':
          print '**********************************************'
          print 'Method: ', key
          callees = call_graph.get(key)
	  for callee in callees:
           print '-->', callee
          print '**********************************************'
	return 


###########################################################################################

###########################################################################################	


def extract_perm_to_context_for_set(set_context_perm):
	res_context_tp = set()
	res_cont_to_perm_tp = {}
	for cont_perm in set_context_perm:
		cont_tp , perm_tp = extract_context_permission(cont_perm)
		if perm_tp in res_cont_to_perm_tp:
			res_cont_to_perm_tp[perm_tp].add(cont_tp)
		else:
			res_cont_to_perm_tp[perm_tp] = set()
			res_cont_to_perm_tp[perm_tp].add(cont_tp)
		
	return res_cont_to_perm_tp


def extract_context_permission_for_set(set_context_perm):
	
	res_context_tp = set()
	res_perm_tp = set()
	for cont_perm in set_context_perm:
		cont_tp , perm_tp = extract_context_permission(cont_perm)
		res_context_tp.add(cont_tp)
		res_perm_tp.add(perm_tp)
		
	return res_context_tp, res_perm_tp



def extract_context_permission_as_pairs_for_set(set_context_perm):
	
	res_context_perm_tp = set()
	res_perm_tp = set()
	for cont_perm in set_context_perm:
		cont_tp , perm_tp = extract_context_permission(cont_perm)
		res_context_perm_tp.add((cont_tp,perm_tp))
		
		
	return res_context_perm_tp




def extract_context_permission(word):
	_match = re.search(r'([^#]+)(#)(.+)', word)
	if(_match):                             
		return (_match.group(1), _match.group(3))			                                    
	else: 	
		return (None,None)                      



def extract_apk_name_for_spec(line):
	_match = re.search(r'(//-----------------------)(\s)(.+)', line)
	if(_match):                             
		return (_match.group(3))
	else:
		return None



def read_spec_file(f_name):	
	check_file_exists(f_name)
	f = open(f_name, 'r')
	
	if f is None:
		sys.exit('Can\'t open file '+file_name)
	global_spec = {}	
        pattern = re.compile('[^\s]+')
	name = None
	spec_tmp = {}

	for line in f:			
		name_tp = extract_apk_name_for_spec(line)
		
		if name_tp != None:
			name = name_tp

		(t,p1,p2) = extract_rule_head_and_tail(line)	
		if t != None:		
			swords = set(pattern.findall(p1))
			key = next(iter(swords))
			assert len(swords) > 0
			swords2 = set(pattern.findall(p2))
			spec_tmp[key] = swords2
			for element in swords2:
				e_tmp = key + '#' + element
							
		if('//----------------------------------------------------------' in line):
			if (len(spec_tmp)>0) and name != None:				
				global_spec[name] = dict(spec_tmp)
				name = None
				spec_tmp.clear()
	
	if (len(spec_tmp)>0) and name != None:		
		global_spec[name] = dict(spec_tmp)	
	f.close()
	return global_spec




def read_spec_file_for_methods(f_name):	
	check_file_exists(f_name)
	f = open(f_name, 'r')
	
	if f is None:
		sys.exit('Can\'t open file '+file_name)
	global_spec = {}	
	pattern = re.compile('[^\s]+')
        # pattern for matching methods 
	pattern_meth = re.compile('[^\s]+\([^\)]*\)[^\s]+')
	name = None
	spec_tmp = {}

	for line in f:			
		name_tp = extract_apk_name_for_spec(line)
		
		if name_tp != None:
			name = name_tp

		(t,p1,p2) = extract_rule_head_and_tail(line)	
		if t != None:		
			swords = set(pattern.findall(p1))
			key = next(iter(swords))
			assert len(swords) > 0
			swords2 = set(pattern_meth.findall(p2))
			spec_tmp[key] = swords2
			for element in swords2:
				e_tmp = key + '#' + element
							
		if('//----------------------------------------------------------' in line):
			if (len(spec_tmp)>0) and name != None:				
				global_spec[name] = dict(spec_tmp)
				name = None
				spec_tmp.clear()
	
	if (len(spec_tmp)>0) and name != None:		
		global_spec[name] = dict(spec_tmp)	
	f.close()
	return global_spec




def read_spec_file2_for_methods(f_name):	
	check_file_exists(f_name)
	f = open(f_name, 'r')
	
	if f is None:
		sys.exit('Can\'t open file '+file_name)
	global_spec = {}	
	pattern = re.compile('[^\s]+')
        # pattern for matching methods 
	pattern_meth = re.compile('[^\s]+\([^\)]*\)[^\s]+')
	name = None	
	spec_tmp = set()

	for line in f:			
		name_tp = extract_apk_name_for_spec(line)
		
		if name_tp != None:
			name = name_tp

		(t,p1,p2) = extract_rule_head_and_tail(line)	
		if t != None:		
			swords = set(pattern.findall(p1))
			key = next(iter(swords))
			assert len(swords) > 0
			swords2 = set(pattern_meth.findall(p2))
			spec_tmp[key] = swords2
			for element in swords2:
				spec_tmp.add()
				e_tmp = key + '#' + element
							
		if('//----------------------------------------------------------' in line):
			if (len(spec_tmp)>0) and name != None:				
				global_spec[name] = set(spec_tmp)
				name = None
				spec_tmp.clear()
	
	if (len(spec_tmp)>0) and name != None:		
		global_spec[name] = dict(spec_tmp)	
	f.close()
	return global_spec



	
def read_spec_file2(f_name):	
	check_file_exists(f_name)
	f = open(f_name, 'r')
	
	if f is None:
		sys.exit('Can\'t open file '+file_name)
	global_spec = {}	
        pattern = re.compile('[^\s]+')
	name = None
	spec_tmp = set()

	for line in f:			
		name_tp = extract_apk_name_for_spec(line)
		
		if name_tp != None:
			name = name_tp

		(t,p1,p2) = extract_rule_head_and_tail(line)	
		if t != None:		
			swords = set(pattern.findall(p1))
			key = next(iter(swords))
			assert len(swords) > 0
			swords2 = set(pattern.findall(p2))						
			for element in swords2:				
				spec_tmp.add(key+'#'+element)			
		if('//----------------------------------------------------------' in line):
			if (len(spec_tmp)>0) and name != None:				
				global_spec[name] = set(spec_tmp)
				name = None
				spec_tmp.clear()
	
	if (len(spec_tmp)>0) and name != None:		
		global_spec[name] = set(spec_tmp)	
	f.close()
	return global_spec




def generate_one_sume_constraint(num_vars):
	res = ""
	for num in range(1,num_vars+1):
		res = res + "  1 "+"x"+str(num)
	return res


def generate_one_pb_problem(map_spec, constraint_op, max_or_min):
	global var_rename
	global var_rename_back
	global global_counter
	coef_objective_function = {}
	set_constraints = set()
	set_variables = set()
	set_objective_function_terms = set()
	
	for entry,spec in map_spec.iteritems():
		constraint_tp = ''
		objective_term = ''
		nb_vars = 0
		for key, val in spec.iteritems():
			for tag in val:
				var = key+'#'+tag
				if var in var_rename:
					var = var_rename[var]
				else:
					new_var = 'x'+str(global_counter)
					global_counter = global_counter + 1
					var_rename[var] = new_var
					var_rename_back[new_var] = var
					var = var_rename[var]
					
				set_variables.add(var)
				if(constraint_op == '<='):
					constraint_tp = constraint_tp +'  -1 '+var
				else:
					constraint_tp = constraint_tp +'  1 '+var
				
				objective_term = objective_term +' '+var
	
				nb_vars = nb_vars + 1
				if var not in coef_objective_function:
					coef_objective_function[var] = 1
				else:
					coef_objective_function[var] = coef_objective_function[var] + 1
		
		set_objective_function_terms.add(objective_term)
		
		if(constraint_op == '<='):
			constraint_tp = constraint_tp +" >= "+str(-(nb_vars-1))
		elif (constraint_op == '>='):
			constraint_tp = constraint_tp +" >= "+str((nb_vars))
		else:
			assert(0)

		set_constraints.add(constraint_tp)
		#print '\n ---------->', entry
		#print constraint_tp
		#print set_variables
		#print objective_function
	#print '*', '#variable=', len(set_variables), '#constraint=', len(set_constraints)  
	objective_function = ''
	#for key, val in coef_objective_function.iteritems():
		#objective_function = objective_function + '   -' +str(val)+' '+key
	for term in set_objective_function_terms:
		if(max_or_min == 'max'):
			objective_function = objective_function + '   -1 ' +term  
		elif (max_or_min == 'min'):
			objective_function = objective_function + '   +1 ' +term
		else:
			assert(0)
			
	#print '\n\n'
	#for constraint in set_constraints:
	#	print constraint, ';'
	#print '\n\n'
	#print 'min : ', objective_function,';'
	return set_constraints, objective_function



def generate_one_pb_z3(map_spec, id_for_app):
	global var_rename
	global var_rename_back
	global global_counter		
	
	app_index = 1
	app_to_constraint_vars = {}

	for entry,spec in map_spec.iteritems():						
		var_per_app = set()
		for key, val in spec.iteritems():
			for tag in val:
				var = key+'#'+tag
				if var in var_rename:
					var = var_rename[var]
				else:
					new_var = 'x'+str(global_counter)
					global_counter = global_counter + 1
					var_rename[var] = new_var
					var_rename_back[new_var] = var
					var = var_rename[var]

				var_per_app.add(var)									
		#constraint_per_app = ' '.join(var_per_app)
		id_tmp = id_for_app + str(app_index)	
		if len(var_per_app) > 0:
			app_to_constraint_vars[id_tmp] = var_per_app
		#constraint_per_app = '(assert (equiv (and ' + constraint_per_app +') ' +id_tmp+' ))'		
		app_index+=1
                
		
	return app_to_constraint_vars
		



def generate_one_pb_problem2(map_spec, constraint_op, max_or_min):
	global var_rename
	global var_rename_back
	global global_counter
	coef_objective_function = {}
	set_constraints = set()
	set_variables = set()
	set_objective_function_terms = set()
	
	for entry,spec in map_spec.iteritems():
		constraint_tp = ''
		objective_term = ''
		nb_vars = 0
		for var in spec:
			
				
				if var in var_rename:
					var = var_rename[var]
				else:
					new_var = 'x'+str(global_counter)
					global_counter = global_counter + 1
					var_rename[var] = new_var
					var_rename_back[new_var] = var
					var = var_rename[var]
					
				set_variables.add(var)
				if(constraint_op == '<='):
					constraint_tp = constraint_tp +'  -1 '+var
				else:
					constraint_tp = constraint_tp +'  1 '+var
				
				objective_term = objective_term +' '+var
	
				nb_vars = nb_vars + 1
				if var not in coef_objective_function:
					coef_objective_function[var] = 1
				else:
					coef_objective_function[var] = coef_objective_function[var] + 1
		
		set_objective_function_terms.add(objective_term)
		
		if(constraint_op == '<='):
			constraint_tp = constraint_tp +" >= "+str(-(nb_vars-1))
		elif (constraint_op == '>='):
			constraint_tp = constraint_tp +" >= "+str((nb_vars))
		else:
			assert(0)

		set_constraints.add(constraint_tp)
		#print '\n ---------->', entry
		#print constraint_tp
		#print set_variables
		#print objective_function
	#print '*', '#variable=', len(set_variables), '#constraint=', len(set_constraints)  
	objective_function = ''
	#for key, val in coef_objective_function.iteritems():
		#objective_function = objective_function + '   -' +str(val)+' '+key
	for term in set_objective_function_terms:
		if(max_or_min == 'max'):
			objective_function = objective_function + '   -1 ' +term  
		elif (max_or_min == 'min'):
			objective_function = objective_function + '   +1 ' +term
		else:
			assert(0)
			
	#print '\n\n'
	#for constraint in set_constraints:
	#	print constraint, ';'
	#print '\n\n'
	#print 'min : ', objective_function,';'
	return set_constraints, objective_function





def generate_whole_pb_problem(f_name, option):
	spec1 = read_spec_file(f_name+'.mal')
	set_constraints_mal, objective_func_mal = generate_one_pb_problem(spec1,'<=','min')
	
	#print set_constraints_mal
	#print objective_func_mal
	spec2 = read_spec_file(f_name+'.ben')
	set_constraints_ben, objective_func_ben = generate_one_pb_problem(spec2,'>=','max')

	if(option == 'conservative'):
		print '*', '#variable=', len(var_rename), '#constraint=', len(set_constraints_mal) 
		print 'min: '+objective_func_ben+';'
		print '\n\n'
		for constraint in set_constraints_mal:
			print constraint, ';'
	elif (option == 'permissive'):
		print '*', '#variable=', len(var_rename), '#constraint=', len(set_constraints_ben) 
		print 'min: '+objective_func_mal+';'
		print '\n\n'
		for constraint in set_constraints_ben:
			print constraint, ';'


def generate_whole_pb_problem2(f_name, option):
	spec1 = read_spec_file(f_name+'.mal')
	set_constraints_mal, objective_func_mal = generate_one_pb_problem(spec1,'<=','min')

	#print set_constraints_mal
	#print objective_func_mal
	spec2 = read_spec_file(f_name+'.ben')
	set_constraints_ben, objective_func_ben = generate_one_pb_problem(spec2,'>=','min')
	
	print '*', '#variable=', len(var_rename), '#constraint=', str(1) 
	print 'min: '+objective_func_mal+';'
	print '\n\n'
	print 'min: '+objective_func_ben+'>= 300 '+';'
	return
	if(option == 'conservative'):
		print '*', '#variable=', len(var_rename), '#constraint=', len(set_constraints_mal) 
		print 'min: '+objective_func_ben+';'
		print '\n\n'
		for constraint in set_constraints_mal:
			print constraint, ';'
	elif (option == 'permissive'):
		print '*', '#variable=', len(var_rename), '#constraint=', len(set_constraints_ben) 
		print 'min: '+objective_func_mal+';'
		print '\n\n'
		for constraint in set_constraints_ben:
			print constraint, ';'


def print_policy_for_latex(policy):
	policy_pairs = extract_context_permission_as_pairs_for_set(policy)
	for context, perm in policy_pairs:
		perm1 = perm.replace("_","\_")
		context1 = context.replace("_","\_")
		print context1, ":  $\\neg$", perm1, " \\\\"


def print_policy(policy):
	policy_pairs = extract_context_permission_as_pairs_for_set(policy)
	for context, perm in policy_pairs:
		
		print context, ":  ~"+perm

def print_policy_to_file(policy, myfile):
	policy_pairs = extract_context_permission_as_pairs_for_set(policy)
	f = open(myfile, 'w')
	if f is None:
		sys.exit('Can\'t open file '+myfile)

	for context, perm in policy_pairs:		
		f.write(context+" :  ~"+perm+'\n')
	
	f.close()



def call_soot(apk_file):
	apk_abs_path = os.path.abspath(apk_file)
	
	## save working dir
	prev_wd = os.getcwd()
	

	## if not in the working dir of EviCheck
	if os.path.dirname(__file__) != '':
		os.chdir(os.path.dirname(__file__)+'/soot')
		
	else:
		os.chdir('./soot')			 			 
		
	
	print '\nCalling soot for parsing apk file: '+apk_file
	print 'Please wait'
	command = 'java -jar InterfaceToSoot.jar -android-jars \.  -process-dir '+ apk_abs_path + ' res_soot.tmp > res.tmp'
	#os.system(command)
	
	#os.system ('mv res_soot.tmp sootCallGraph.py')
	#os.system ('cp sootCallGraph.py ../EvichekFiles')
	#os.system ('rm sootCallGraph.py')
	## remove temp file ####################		
	if os.path.isfile('res_soot.tmp'):
		os.remove('res_soot.tmp')

	if os.path.isfile('res.tmp'):
		os.remove('res.tmp')

	if os.path.isdir('sootOutput'):
		os.rmdir('sootOutput') 
		

	os.chdir(prev_wd)
	#import_module('EvichekFiles.sootCallGraph')
	my_module = importlib.import_module('EvichekFiles.sootCallGraph')
	CALL_GRAPH_FROM_SOOT = my_method = getattr(my_module, "CALL_GRAPH_FROM_SOOT")	
	return CALL_GRAPH_FROM_SOOT
        #sys.exit(0)			 
	

###########################################################################################

###########################################################################################


def generate_whole_pb_problem_z3(f_name,  p_file):

	## Read the spec files #################
	
	spec_ben = read_spec_file(f_name+'.ben')	
	app_constraints_ben = generate_one_pb_z3(spec_ben,'b')
	
	declar_vars = set()
	assertions = set()
	mal_objective_terms = set()
	ben_objective_terms = set()
	bool_to_int_fun_name = 'bool_to_int'
	bool_to_int_fun_def = '(define-fun bool_to_int ((b Bool)) Int (ite b 1 0))'
	for key, val in app_constraints_ben.iteritems():
		declar_vars.add(key)
		declar_vars.update(val)
		constraint_per_app = ' '.join(val)
		constraint_per_app = '(assert (equiv (and ' + constraint_per_app +') ' +key+'))'
		assertions.add(constraint_per_app)
		ben_objective_terms.add('('+bool_to_int_fun_name +' '+key+')')

		
	spec_mal = read_spec_file(f_name+'.mal')
	app_constraints_mal = generate_one_pb_z3(spec_mal,'m')
	for key, val in app_constraints_mal.iteritems():
		declar_vars.add(key)
		declar_vars.update(val)
		constraint_per_app = ' '.join(val)
		constraint_per_app = '(assert (equiv (and ' + constraint_per_app +') ' +key+'))'
		assertions.add(constraint_per_app)
		mal_objective_terms.add('('+bool_to_int_fun_name +' '+key+')')


	# declaration part

	problem = ''
	for v in declar_vars:
		problem = problem+'\n'+'(declare-const '+v+' Bool)'


	# conversion function
	problem = problem + '\n\n\n' + bool_to_int_fun_def + '\n\n\n'
	

	for a in assertions:
		problem = problem + '\n' + a
		
	problem  = problem + '\n\n\n'

	# objective function
	obj_fun_ben_part = '(+ '+' '.join(ben_objective_terms)+')'
	obj_fun_mal_part = '(+ '+' '.join(mal_objective_terms)+')'
	problem  = problem + '(maximize (- '+obj_fun_ben_part+' '+obj_fun_mal_part+'))'
	problem  = problem + '\n\n\n'
	


	# commands needed by z3
	problem = problem + '\n(check-sat)\n(get-model)'
	

	print problem
	#print len(app_constraints_ben)
	#print len(app_constraints_mal)

	########################################
	prev_wd = os.getcwd()
	#if 'EVI_DIR' in os.environ:
		#os.chdir(os.environ['EVI_DIR'])
	if os.path.dirname(__file__) != '':
		os.chdir(os.path.dirname(__file__))
	## Preparing the problem for the sat4j##
	f = open('pb.tmp', 'w')
	if f is None:
		sys.exit('Can\'t open file '+file_name)
	
	f.write(problem)
	f.close()

	########################################

	##  z3 invoked  #####################
	print '\nProblem sent to the constraint solver'
	print 'Please wait, the constraint solver can take several minutes'

	command = './solver/z3 '+'pb.tmp > res.tmp'
	#os.chdir(os.environ['EVI_DIR'])
	#if 'EVI_DIR' in os.environ: 
		#command = 'java -jar '+ os.environ['EVI_DIR'] +'/solver/sat4j-pb.jar '+'pb.tmp > res.tmp'
		
	#os.system('java -jar ./solver/sat4j-pb.jar '+'pb.tmp > res.tmp')
	os.system(command)
	########################################

	#### processing sa4j's answer ##########
	with open ("res.tmp", "r") as myfile:
		sol=myfile.read()
		#print 'SOL: ', sol
		sol =  extract_solution_from_z3(sol)
		if sol is None:
			sys.exit('\nNo solution found by the constraint solver!')
			
	var_coef = get_vars_in_z3_sol(sol)
	res_tmp = set()
	for var, coef in var_coef.iteritems():
		if coef ==0 and var not in app_constraints_ben and var not in app_constraints_mal:
			res_tmp.add(var_rename_back[var])
	#########################################
	
	## remove temp files ####################		
	if os.path.isfile('pb.tmp'):
		os.remove('pb.tmp')
	if os.path.isfile('res.tmp'):
		os.remove('res.tmp')
	#########################################	

	## finally print the policy in EviCheck's format
	os.chdir(prev_wd)	
	print "\n\n=================================="
	print "Policy generated:\n"
	print_policy(res_tmp)
	print_policy_to_file(res_tmp, p_file)
	print "\n=================================="
	return



def CountPERMSInSpecs(f_name):
        
        all_apis = set()
        
        c = 0
        spec = read_spec_file(f_name+'.ben')
        for f, s in spec.iteritems():
                for context, methods in s.iteritems():
                        all_apis.update(set([context+'_'+m for m in methods]))

        print len(all_apis)
        
        spec = read_spec_file(f_name+'.mal')      
        for f, s in spec.iteritems():
                for context, methods in s.iteritems():
                        all_apis.update(set([context+'_'+m for m in methods]))
                                                
        
        print len(all_apis)

def CountApiInSpecs(f_name):
        
        all_apis = set()
        
        c = 0
        spec = read_spec_file_for_methods(f_name+'.ben')
        for f, s in spec.iteritems():
                for context, methods in s.iteritems():
                        all_apis.update(set([context+'_'+m for m in methods]))

        print len(all_apis)
        
        spec = read_spec_file_for_methods(f_name+'.mal')          
        for f, s in spec.iteritems():
                for context, methods in s.iteritems():
                        all_apis.update(set([context+'_'+m for m in methods]))
                                                
        
        print len(all_apis)




def generate_whole_pb_problem_z3_api(f_name,  p_file):

	## Read the spec files #################
	
	spec_ben = read_spec_file_for_methods(f_name+'.ben')	

	app_constraints_ben = generate_one_pb_z3(spec_ben,'b')
	
	declar_vars = set()
	assertions = set()
	mal_objective_terms = set()
	ben_objective_terms = set()
	bool_to_int_fun_name = 'bool_to_int'
	bool_to_int_fun_def = '(define-fun bool_to_int ((b Bool)) Int (ite b 1 0))'
	for key, val in app_constraints_ben.iteritems():
		declar_vars.add(key)
		declar_vars.update(val)
		constraint_per_app = ' '.join(val)
		constraint_per_app = '(assert (equiv (and ' + constraint_per_app +') ' +key+'))'
		assertions.add(constraint_per_app)
		ben_objective_terms.add('('+bool_to_int_fun_name +' '+key+')')

		
	spec_mal = read_spec_file_for_methods(f_name+'.mal')
	app_constraints_mal = generate_one_pb_z3(spec_mal,'m')
	for key, val in app_constraints_mal.iteritems():
		declar_vars.add(key)
		declar_vars.update(val)
		constraint_per_app = ' '.join(val)
		constraint_per_app = '(assert (equiv (and ' + constraint_per_app +') ' +key+'))'
		assertions.add(constraint_per_app)
		mal_objective_terms.add('('+bool_to_int_fun_name +' '+key+')')


	# declaration part

	problem = ''
	for v in declar_vars:
		problem = problem+'\n'+'(declare-const '+v+' Bool)'


	# conversion function
	problem = problem + '\n\n\n' + bool_to_int_fun_def + '\n\n\n'
	

	for a in assertions:
		problem = problem + '\n' + a
		
	problem  = problem + '\n\n\n'

	# objective function
	obj_fun_ben_part = '(+ '+' '.join(ben_objective_terms)+')'
	obj_fun_mal_part = '(+ '+' '.join(mal_objective_terms)+')'
        problem  = problem + '\n\n\n'
        #problem  = problem + '(assert (< '+obj_fun_mal_part +' 88 ))'
        #b_tmp = str(len(app_constraints_ben))
        #problem  = problem + '(assert (>= '+obj_fun_ben_part +' '+ b_tmp +'))'
        #problem  = problem + '(maximize (- '+obj_fun_mal_part +'))'
        problem  = problem + '\n\n\n'
	problem  = problem + '(maximize (- '+obj_fun_ben_part+' '+obj_fun_mal_part+'))'
	problem  = problem + '\n\n\n'
	


	# commands needed by z3
	problem = problem + '\n(check-sat)\n(get-model)'
	

	print problem
	#print len(app_constraints_ben)
	#print len(app_constraints_mal)

	########################################
	prev_wd = os.getcwd()
	#if 'EVI_DIR' in os.environ:
		#os.chdir(os.environ['EVI_DIR'])
	if os.path.dirname(__file__) != '':
		os.chdir(os.path.dirname(__file__))
	## Preparing the problem for the sat4j##
	f = open('pb.tmp', 'w')
	if f is None:
		sys.exit('Can\'t open file '+file_name)
	
	f.write(problem)
	f.close()

	########################################

	##  z3 invoked  #####################
	print '\nProblem sent to the constraint solver'
	print 'Please wait, the constraint solver can take several minutes'

	command = 'nice ./solver/z3 '+'pb.tmp > res.tmp'
	#os.chdir(os.environ['EVI_DIR'])
	#if 'EVI_DIR' in os.environ: 
		#command = 'java -jar '+ os.environ['EVI_DIR'] +'/solver/sat4j-pb.jar '+'pb.tmp > res.tmp'
		
	#os.system('java -jar ./solver/sat4j-pb.jar '+'pb.tmp > res.tmp')
	os.system(command)
	########################################

	#### processing sa4j's answer ##########
	with open ("res.tmp", "r") as myfile:
		sol=myfile.read()
		#print 'SOL: ', sol
		sol =  extract_solution_from_z3(sol)
		if sol is None:
			sys.exit('\nNo solution found by the constraint solver!')
			
	var_coef = get_vars_in_z3_sol(sol)
	res_tmp = set()
	for var, coef in var_coef.iteritems():
		if coef ==0 and var not in app_constraints_ben and var not in app_constraints_mal:
			res_tmp.add(var_rename_back[var])
	#########################################
	
	## remove temp files ####################		
	if os.path.isfile('pb.tmp'):
		os.remove('pb.tmp')
	if os.path.isfile('res.tmp'):
		os.remove('res.tmp')
	#########################################	

	## finally print the policy in EviCheck's format
	os.chdir(prev_wd)	
	print "\n\n=================================="
	print "Policy generated:\n"
	print_policy(res_tmp)
	print_policy_to_file(res_tmp, p_file)
	print "\n=================================="
	return







def generate_whole_pb_problem_z3_api_iter(f_name,  p_file):

	## Read the spec files #################

        mal_family_to_spec = {}
        spec_ben = read_spec_file_for_methods(f_name)
        print len(spec_ben)
        
        
        for n in spec_ben:
                match = re.search(r'(drebin-all/)((\W|\w)+)(/)', n)
                if match:
                        mal_name = match.group(2)
                        if mal_name not in mal_family_to_spec:
                                mal_family_to_spec[mal_name] = {n:spec_ben[n]}
                        else:
                                mal_family_to_spec[mal_name][n] = spec_ben[n]
                        
        print len(mal_family_to_spec)
        sys.exit(0)
	
	spec_ben = read_spec_file_for_methods(f_name+'.ben')	

	app_constraints_ben = generate_one_pb_z3(spec_ben,'b')
	
       	declar_vars = set()
	assertions = set()
	mal_objective_terms = set()
	ben_objective_terms = set()
	bool_to_int_fun_name = 'bool_to_int'
	bool_to_int_fun_def = '(define-fun bool_to_int ((b Bool)) Int (ite b 1 0))'
        
        

	for key, val in app_constraints_ben.iteritems():
		declar_vars.add(key)
		declar_vars.update(val)
		constraint_per_app = ' '.join(val)
		constraint_per_app = '(assert (equiv (and ' + constraint_per_app +') ' +key+'))'
		assertions.add(constraint_per_app)
		ben_objective_terms.add('('+bool_to_int_fun_name +' '+key+')')

		
	spec_mal = read_spec_file_for_methods(f_name+'.mal')
	app_constraints_mal = generate_one_pb_z3(spec_mal,'m')
	for key, val in app_constraints_mal.iteritems():
		declar_vars.add(key)
		declar_vars.update(val)
		constraint_per_app = ' '.join(val)
		constraint_per_app = '(assert (equiv (and ' + constraint_per_app +') ' +key+'))'
		assertions.add(constraint_per_app)
		mal_objective_terms.add('('+bool_to_int_fun_name +' '+key+')')




        ###############################################################
        ## TEMPS TEST PART

        intersect_mal = set()
        count = 0
        for key, val in app_constraints_mal.iteritems():
                for key2, val2 in app_constraints_ben.iteritems():
                        if val.issubset(val2):
                                print val2
                                print val
                                print '!!!!!!!!!!!!!!!!!!!!!!!!!!!!1'
                                intersect_mal.add(key)
                                count += 1
                                break
        print intersect_mal

        for e in intersect_mal:
                del app_constraints_mal[e]

        count2 = 0
        list_diff = []
        for key, val in app_constraints_mal.iteritems():
                for key2, val2 in app_constraints_ben.iteritems():
                        list_diff.append(val2.difference(val))
                        if val.issubset(val2):
                                #print val2
                                #print val
                                
                                print '!!!!!!!!!!!!!!!!!!!!!!!!!!!!----'
                                intersect_mal.add(key)
                                count2 += 1
                                break
                

        print count
        print count2
        for d in list_diff:
                print d
        sys.exit(0)
        ###############################################################



	# declaration part

	problem = ''
	for v in declar_vars:
		problem = problem+'\n'+'(declare-const '+v+' Bool)'


	# conversion function
	problem = problem + '\n\n\n' + bool_to_int_fun_def + '\n\n\n'
	

	for a in assertions:
		problem = problem + '\n' + a
		
	problem  = problem + '\n\n\n'

	# objective function
	obj_fun_ben_part = '(+ '+' '.join(ben_objective_terms)+')'
	obj_fun_mal_part = '(+ '+' '.join(mal_objective_terms)+')'
        problem  = problem + '\n\n\n'
        #problem  = problem + '(assert (< '+obj_fun_mal_part +' 88 ))'
        #b_tmp = str(len(app_constraints_ben))
        #problem  = problem + '(assert (>= '+obj_fun_ben_part +' '+ b_tmp +'))'
        #problem  = problem + '(maximize (- '+obj_fun_mal_part +'))'
        problem  = problem + '\n\n\n'
	problem  = problem + '(maximize (- '+obj_fun_ben_part+' '+obj_fun_mal_part+'))'
	problem  = problem + '\n\n\n'
	


	# commands needed by z3
	problem = problem + '\n(check-sat)\n(get-model)'
	

	print problem
	#print len(app_constraints_ben)
	#print len(app_constraints_mal)

	########################################
	prev_wd = os.getcwd()
	#if 'EVI_DIR' in os.environ:
		#os.chdir(os.environ['EVI_DIR'])
	if os.path.dirname(__file__) != '':
		os.chdir(os.path.dirname(__file__))
	## Preparing the problem for the sat4j##
	f = open('pb.tmp', 'w')
	if f is None:
		sys.exit('Can\'t open file '+file_name)
	
	f.write(problem)
	f.close()

	########################################

	##  z3 invoked  #####################
	print '\nProblem sent to the constraint solver'
	print 'Please wait, the constraint solver can take several minutes'

	command = 'nice ./solver/z3 '+'pb.tmp > res.tmp'
	#os.chdir(os.environ['EVI_DIR'])
	#if 'EVI_DIR' in os.environ: 
		#command = 'java -jar '+ os.environ['EVI_DIR'] +'/solver/sat4j-pb.jar '+'pb.tmp > res.tmp'
		
	#os.system('java -jar ./solver/sat4j-pb.jar '+'pb.tmp > res.tmp')
	os.system(command)
	########################################

	#### processing sa4j's answer ##########
	with open ("res.tmp", "r") as myfile:
		sol=myfile.read()
		#print 'SOL: ', sol
		sol =  extract_solution_from_z3(sol)
		if sol is None:
			sys.exit('\nNo solution found by the constraint solver!')
			
	var_coef = get_vars_in_z3_sol(sol)
	res_tmp = set()
        encoded_vars = set()
	for var, coef in var_coef.iteritems():
		if coef ==0 and var[0] == 'x':#var not in app_constraints_ben and var not in app_constraints_mal:
			res_tmp.add(var_rename_back[var])
                        encoded_vars.add(var)
	#########################################
	
        count3 = 0
        for key, val in app_constraints_ben.iteritems():
                if len(val.intersection(encoded_vars)) > 0:
                        count3 += 1
                        

        print count3
        print len(app_constraints_mal)
        sys.exit(0)


   	## remove temp files ####################		
	if os.path.isfile('pb.tmp'):
		os.remove('pb.tmp')
	if os.path.isfile('res.tmp'):
		os.remove('res.tmp')
	#########################################	

	## finally print the policy in EviCheck's format
	os.chdir(prev_wd)	
	print "\n\n=================================="
	print "Policy generated:\n"
	#print_policy(res_tmp)
	print_policy_to_file(res_tmp, p_file)
	print "\n=================================="
	return






def generate_whole_pb_problem_with_numb_rules(f_name, option, num_rules, p_file):

	## Read the spec files #################
	
	spec1 = read_spec_file(f_name+'.mal')
	set_constraints_mal, objective_func_mal = generate_one_pb_problem(spec1,'<=','min')
	spec2 = read_spec_file(f_name+'.ben')
	set_constraints_ben, objective_func_ben = generate_one_pb_problem(spec2,'>=','min')
	########################################
	prev_wd = os.getcwd()
	#if 'EVI_DIR' in os.environ:
		#os.chdir(os.environ['EVI_DIR'])
	if os.path.dirname(__file__) != '':
		os.chdir(os.path.dirname(__file__))
	## Preparing the problem for the sat4j##
	f = open('pb.tmp', 'w')
	if f is None:
		sys.exit('Can\'t open file '+file_name)
	f.write( '* '+ ' #variable= '+ str(len(var_rename))+ ' #constraint= '+str(1))
	f.write ('\nmin: '+objective_func_mal+';'+'\n\n')

	#print objective_func_ben+'>= 300 '+';'
	bound_ben = len(spec2)*2/3
	f.write(objective_func_ben+'>= '+ str(bound_ben) +';')
	f.close()

	########################################

	##  sat4j invoked  #####################
	print '\nProblem sent to the constraint solver'
	print 'Please wait, the constraint solver can take several minutes'

	command = 'java -jar ./solver/sat4j-pb.jar '+'pb.tmp > res.tmp'
	#os.chdir(os.environ['EVI_DIR'])
	#if 'EVI_DIR' in os.environ: 
		#command = 'java -jar '+ os.environ['EVI_DIR'] +'/solver/sat4j-pb.jar '+'pb.tmp > res.tmp'
		
	#os.system('java -jar ./solver/sat4j-pb.jar '+'pb.tmp > res.tmp')
	os.system(command)
	########################################

	#### processing sa4j's answer ##########
	with open ("res.tmp", "r") as myfile:
		sol=myfile.read()
		#print 'SOL: ', sol
		sol =  extract_solution_from_sat4j(sol)
		if sol is None:
			sys.exit('\nNo solution found by the constraint solver!')
			
	var_coef = get_vars_in_pbs_sol(sol)
	res_tmp = set()
	for var, coef in var_coef.iteritems():
		if coef == 0:
			res_tmp.add(var_rename_back[var])
	#########################################
	
	## remove temp files ####################		
	if os.path.isfile('pb.tmp'):
		os.remove('pb.tmp')
	if os.path.isfile('res.tmp'):
		os.remove('res.tmp')
	#########################################	

	## finally print the policy in EviCheck's format
	os.chdir(prev_wd)	
	print "\n\n=================================="
	print "Policy generated:\n"
	print_policy(res_tmp)
	print_policy_to_file(res_tmp, p_file)
	print "\n=================================="
	return



def generate_whole_pb_problem_with_numb_rules2(f_name, option, num_rules):

	## Read the spec files #################
	
	spec1 = read_spec_file(f_name+'.mal')
	set_constraints_mal, objective_func_mal = generate_one_pb_problem(spec1,'<=','min')
	spec2 = read_spec_file(f_name+'.ben')
	set_constraints_ben, objective_func_ben = generate_one_pb_problem(spec2,'>=','min')
	########################################
	prev_wd = os.getcwd()
	#if 'EVI_DIR' in os.environ:
		#os.chdir(os.environ['EVI_DIR'])
	os.chdir(os.path.dirname(__file__))
	## Preparing the problem for the sat4j##
	f = open('pb.tmp', 'w')
	if f is None:
		sys.exit('Can\'t open file '+file_name)
	f.write( '* '+ ' #variable= '+ str(len(var_rename))+ ' #constraint= '+str(1))
	f.write ('\nmin: '+objective_func_mal+';'+'\n\n')

	#print objective_func_ben+'>= 300 '+';'
	bound_ben = len(spec2)*2/3
	f.write(objective_func_ben+'>= '+ str(bound_ben) +';')
	f.close()

	########################################

	##  sat4j invoked  #####################
	print '\nProblem sent to the constraint solver'
	print 'Please wait, the constraint solver can take several minutes'

	command = 'java -jar ./solver/sat4j-pb.jar '+'pb.tmp > res.tmp'
	#os.chdir(os.environ['EVI_DIR'])
	#if 'EVI_DIR' in os.environ: 
		#command = 'java -jar '+ os.environ['EVI_DIR'] +'/solver/sat4j-pb.jar '+'pb.tmp > res.tmp'
		
	#os.system('java -jar ./solver/sat4j-pb.jar '+'pb.tmp > res.tmp')
	os.system(command)
	########################################

	#### processing sa4j's answer ##########
	with open ("res.tmp", "r") as myfile:
		sol=myfile.read()
		#print 'SOL: ', sol
		sol =  extract_solution_from_sat4j(sol)
		if sol is None:
			sys.exit('\nNo solution found by the constraint solver!')
			
	var_coef = get_vars_in_pbs_sol(sol)
	res_tmp = set()
	for var, coef in var_coef.iteritems():
		if coef == 0:
			res_tmp.add(var_rename_back[var])
	#########################################
	
	## remove temp files ####################		
	if os.path.isfile('pb.tmp'):
		os.remove('pb.tmp')
	if os.path.isfile('res.tmp'):
		os.remove('res.tmp')
	#########################################	

	## finally print the policy in EviCheck's format
	os.chdir(prev_wd)	
	print "\n\n=================================="
	print "Policy generated:\n"
	print_policy(res_tmp)
	print "\n=================================="
	return



def generate_whole_pb_problem3(spec1, spec2, option):
		
	set_constraints_mal, objective_func_mal = generate_one_pb_problem2(spec1,'<=','min')
	
	#print set_constraints_mal
	#print objective_func_mal
	
	set_constraints_ben, objective_func_ben = generate_one_pb_problem2(spec2,'>=','max')

	if(option == 'conservative'):
		print '*', '#variable=', len(var_rename), '#constraint=', len(set_constraints_mal) 
		print 'min: '+objective_func_ben+';'
		print '\n\n'
		for constraint in set_constraints_mal:
			print constraint, ';'
	elif (option == 'permissive'):
		print '*', '#variable=', len(var_rename), '#constraint=', len(set_constraints_ben) 
		print 'min: '+objective_func_mal+';'
		print '\n\n'
		for constraint in set_constraints_ben:
			print constraint, ';'


def generate_whole_pb_problem4(spec1, spec2, option):
		
	set_constraints_mal, objective_func_mal = generate_one_pb_problem2(spec1,'<=','min')

	#print set_constraints_mal
	#print objective_func_mal
	
	set_constraints_ben, objective_func_ben = generate_one_pb_problem2(spec2,'>=','min')
	
	print '*', '#variable=', len(var_rename), '#constraint=', str(1) 
	print 'min: '+objective_func_mal+';'
	print '\n\n'
	print 'min: '+objective_func_ben+'>= 300 '+';'
	return
	if(option == 'conservative'):
		print '*', '#variable=', len(var_rename), '#constraint=', len(set_constraints_mal) 
		print 'min: '+objective_func_ben+';'
		print '\n\n'
		for constraint in set_constraints_mal:
			print constraint, ';'
	elif (option == 'permissive'):
		print '*', '#variable=', len(var_rename), '#constraint=', len(set_constraints_ben) 
		print 'min: '+objective_func_mal+';'
		print '\n\n'
		for constraint in set_constraints_ben:
			print constraint, ';'



def map_back_result_from_pbs(f_name, option, f_from_pbs):
	spec1 = read_spec_file(f_name+'.mal')
	set_constraints_mal, objective_func_mal = generate_one_pb_problem(spec1,'<=','min')

	spec2 = read_spec_file(f_name+'.ben')
	set_constraints_ben, objective_func_ben = generate_one_pb_problem(spec2,'>=','min')
	pbs_solution = read_res_from_pbs(f_from_pbs)
	
	res_tmp = set()
	for var, coef in pbs_solution.iteritems():
		if coef == 0:
			res_tmp.add(var_rename_back[var])
			
	print res_tmp
	print "SIZE", len(res_tmp)
	
	

def read_res_from_pbs(f_name):
	check_file_exists(f_name)
	f = open(f_name,'r')
	if f is None:
		sys.exit('Can\'t open file '+f_name)
	pattern = re.compile('[^\s]+')
	
	var_to_weight = {}
	for line in f:		
		lwords = pattern.findall(line)
		for word in lwords:
			if word[0] == '-':
				key = word[1:len(word)]
				var_to_weight[key] = 0
			else:
				var_to_weight[word] = 1

	return var_to_weight


def get_vars_in_pbs_sol(sol):
	pattern = re.compile('[^\s]+')
	lwords = pattern.findall(sol)
	var_to_weight = {}
	for word in lwords:
		if word[0] == '-':
			key = word[1:len(word)]
			var_to_weight[key] = 0
		else:
			var_to_weight[word] = 1

	return var_to_weight

def get_vars_in_z3_sol(sol):
	pattern = re.compile('(define-fun\s)([^\s]+)(.*\n[\s]*)(.*)(\))')
	my_tuples = pattern.findall(sol)

	var_to_weight = {}
	for t in my_tuples:
		print t[1],' ', t[3] 
		if t[3] == 'true':
			var_to_weight[t[1]] = 1	
		else:
			var_to_weight[t[1]] = 0
			
	return var_to_weight

###########################################################################################

###########################################################################################	

def read_certificate(file_name):
        tag_map.clear()
	check_file_exists(file_name)
	f = open(file_name, 'r')
        pattern = re.compile('[^\s]+')
	
	for line in f:	
		(p1, p2) = extract_cert_key_and_val(line)                
		if p1 is None:
			print 'Certifcate format invalid!'
			print 'Line: ', line			
			sys.exit(0)

		key = p1.strip()
		swords = set(pattern.findall(p2))
		
		
		tag_map[key] = swords
		#print '\n\n----------------------------'
		#print 'LINE: ', line
		#print 'REG: ', key, tag_map[key]


def read_certificate2(file_name):
        tag_map.clear()
	f = open(file_name, 'r')
        pattern = re.compile('[^\s]+')
	
	for line in f:					
                key = ''
                tag_set = set()	
		lwords = pattern.findall(line)
		for word in lwords:
			if(word[len(word)-1] == ':'):
				key = word[0:len(word)-1]

			else:
				tag_set.add(word)

		if key == '':
			sys.exit('Certifcate format invalid')
		
		tag_map[key] = tag_set
		print '\n\n----------------------------'
		print 'LINE: ', line
		print 'REG: ', key, tag_map[key]



# Checking if the policy is satisfied. In principle this should be invoked after the map tag get populated
 
def check_policy(file_name):
	rule_num = 0
	methods_in_app = all_methods
	#print methods_in_app
	policy = read_policy(file_name)
	#print policy
#	for (rule_head, rule_tail) in policy:
#		print '\n ==========================================================='
#		print 'HEAD:', rule_head
#		print 'TAIL:', rule_tail
#		entries = evaluate_rule_head(rule_head,  methods_in_app)
#		print 'EVAL gives:\n ', entries
#		print '\n ==========================================================='
	#return
	policy_violated = 0
	
	for (rule_type, rule_head, rule_tail) in policy:
		rule_num = rule_num + 1
		# get entries to test
		if rule_type == 'and':
			rule_violated = 0
			entries = evaluate_rule_head(rule_head,  methods_in_app)
			for entry in entries:
				# in principle this test is not necessary
				if entry in tag_map:
					exit_loop = 0
					for tag in rule_tail:
						if tag[0] == '~':
							if(len(tag)> 1):
								if tag[1:len(tag)] in tag_map[entry]:
									print '\nRule', rule_num, ' ==> ', rule_head,':',rule_tail
									print 'Policy violated! Tag '+ tag[1:len(tag)] +' is in '+ entry+'\n'
									exit_loop = 1
									policy_violated = 1
									rule_violated = 1
									break
								
						else:
							if tag not in tag_map[entry]:
								print '\nRule', rule_num, ' ==> ', rule_head,':',rule_tail
								print 'Policy violated! Tag '+ tag +' is not in '+ entry+'\n'
								exit_loop = 1
								policy_violated = 1
								rule_violated = 1
								break
									
					if exit_loop == 1: break
                        if len(entries) == 0:                                
                                print '\nWARNING!!!: Rule', rule_num, ' ==> ', rule_head,':',rule_tail
                                print 'vacuously valid as no method matches its context\n'
			if rule_violated == 0:
				satisfied_rules.append('Y')
			else:
				satisfied_rules.append('N')
			

		elif rule_type == 'or':
			entries = evaluate_rule_head(rule_head,  methods_in_app)
			rule_violated = 0
			for entry in entries:
				# in principle this test is not necessary
				if entry in tag_map:
					exit_loop = 0
					for tag in rule_tail:
						if tag[0] == '~':
							if(len(tag)> 1):
								if tag[1:len(tag)] not in tag_map[entry]:
									#print 'Rule', rule_num, ' ==> ', rule_head,':',rule_tail
									#print 'Policy violated! Tag '+ tag[1:len(tag)] +' is in '+ entry+'\n'
									exit_loop = 1									
									break
								
						else:
							if tag in tag_map[entry]:
								#print 'Rule', rule_num, ' ==> ', rule_head,':',rule_tail
								#print 'Policy violated! Tag '+ tag +' is not in '+ entry+'\n'
								exit_loop = 1									      
								break
												
					if exit_loop == 0:
						print '\nRule', rule_num, ' ==> ', rule_head,':V',rule_tail
						print 'Policy violated!\n'
						policy_violated = 1
						rule_violated = 1
						break
			if rule_violated == 0:
				satisfied_rules.append('Y')
			else:
				satisfied_rules.append('N')
					
	if policy_violated == 0:
		print '\nPolicy valid!'
	else:
		print '\nPolicy violated!'

			


###########################################################################################

###########################################################################################




###########################################################################################

###########################################################################################

def TypeMethod1 (method):
	m_type = ()
	for key, val in type_to_setmethods.iteritems():
		if method in val:			
			m_type = m_type+ (key,)			
	return m_type



def GenerateTypeToTagMap1():	
	type_to_tag_map = {}
	for key,val in tag_map.iteritems():
		
		type_tmp = TypeMethod1(key)
	
		if len(type_tmp) > 0:			
			if type_tmp in type_to_tag_map:
				type_to_tag_map[type_tmp] = type_to_tag_map[type_tmp].union(val)
			else:
				type_to_tag_map[type_tmp] = val
	print type_to_tag_map
	return type_to_tag_map

############################################################################################

def TypeMethod (method):
	m_type = set()
	for key, val in type_to_setmethods.iteritems():
		if method in val:			
			m_type.add(key)			
	return m_type


def GenerateTypeToTagMap():	
	type_to_tag_map = {}
	for key,val in tag_map.iteritems():
		
		type_tmp = TypeMethod(key)
	
		for type_part in type_tmp:			
			if type_part in type_to_tag_map:
				type_to_tag_map[type_part] = type_to_tag_map[type_part].union(val)
			else:
				type_to_tag_map[type_part] = val
	return type_to_tag_map


def PrintTypeToTagMap_To_File_in_append_mode(file_n, type_to_tag_map):	
	f = open(file_n, 'a')
	f.write('\n\n\n//----------------------------------------------------------')
	f.write('\n//----------------------- '+file_name)
	f.write('\n//----------------------------------------------------------\n')
	for key, val in type_to_tag_map.iteritems():
		f.write(key+' : ')
		for tag in val:
			f.write(tag+' ')
		
		f.write('\n')

def PrintTypeToTagMap_To_File_in_append_mode2(file_n, file_name, type_to_tag_map):	
	f = open(file_n, 'a')
	f.write('\n\n\n//----------------------------------------------------------')
	f.write('\n//----------------------- '+file_name)
	f.write('\n//----------------------------------------------------------\n')
	for key, val in type_to_tag_map.iteritems():
		f.write(key+' : ')
		for tag in val:
			f.write(tag+' ')
		
		f.write('\n')


def PrintTypeToTagMap_To_File(file_n, type_to_tag_map):	
	print 'CCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCc'
	f = open(file_n, 'w')
	f.write('\n\n\n//----------------------------------------------------------')
	f.write('\n//----------------------- '+file_name)
	f.write('\n//----------------------------------------------------------\n')
	for key, val in type_to_tag_map.iteritems():
		f.write(key+' : ')
		for tag in val:
			f.write(tag+' ')
		
		f.write('\n')


###########################################################################################

###########################################################################################		
		
	



# interpret an element of a rule head, it can be a predefined variable or a method id
def interpret_head_element(elem, list_methods):
	stemp = set(list_methods)
	if elem == EVICHECK_ENTRY_POINT:
		return stemp.intersection(entry_points)
	elif elem == '~'+EVICHECK_ENTRY_POINT:
		return stemp.difference(entry_points)
	elif elem == EVICHECK_ACTIVITY_METHOD:
		return stemp.intersection(activities_methods)
	elif elem == '~'+EVICHECK_ACTIVITY_METHOD:
		return stemp.difference(activities_methods)
	elif elem == EVICHECK_SERVICE_METHOD:
		return stemp.intersection(services_methods)
	elif elem == '~'+EVICHECK_SERVICE_METHOD:
		return stemp.difference(services_methods)
	elif elem == EVICHECK_RECEIVER_METHOD:
		return stemp.intersection(receivers_methods)
	elif elem == '~'+EVICHECK_RECEIVER_METHOD:
		return stemp.difference(receivers_methods)
	elif elem == EVICHECK_ONCLICK_HANDLER:
		return stemp.intersection(onclick_methods)
	elif elem == '~'+EVICHECK_ONCLICK_HANDLER:
		return stemp.difference(onclick_methods)
	elif elem == EVICHECK_ONTOUCH_HANDLER:
		return stemp.intersection(ontouch_methods)
	elif elem == '~'+EVICHECK_ONTOUCH_HANDLER:
		return stemp.difference(ontouch_methods)
	elif elem == EVICHECK_DO_INBACKGROUND:
		return stemp.intersection(do_inbackground_methods)
	elif elem == '~'+EVICHECK_DO_INBACKGROUND:
		return stemp.difference(do_inbackground_methods)
	elif elem == EVICHECK_PAUSE_METHOD:
		return stemp.intersection(on_pause_methods)
	elif elem == '~'+EVICHECK_PAUSE_METHOD:
		return stemp.difference(on_pause_methods)
        elif elem == EVICHECK_ONCREATE_METHOD:
		return stemp.intersection(on_create_methods)
	elif elem == '~'+EVICHECK_ONCREATE_METHOD:
		return stemp.difference(on_create_methods)
        elif elem == EVICHECK_START_METHOD:
		return stemp.intersection(on_start_methods)
	elif elem == '~'+EVICHECK_START_METHOD:
		return stemp.difference(on_start_methods)
        elif elem == EVICHECK_RESUME_METHOD:
		return stemp.intersection(on_resume_methods)
	elif elem == '~'+EVICHECK_RESUME_METHOD:
		return stemp.difference(on_resume_methods)
        elif elem == EVICHECK_DESTROY_METHOD:
		return stemp.intersection(on_destroy_methods)
	elif elem == '~'+EVICHECK_DESTROY_METHOD:
		return stemp.difference(on_destroy_methods)
        


	elif elem[0] == '~':
		if len(elem) > 1:
			m_name = elem[1:len(elem)]
			if (m_name in stemp):
				stemp.remove(m_name)
			return stemp
		else:
			stemp.clear()
			return stemp
	else:
		stemp.clear()
		stemp.add(elem)
		return stemp


# returns the set corresponding to the method head
def evaluate_rule_head(head, list_methods):
	stemp = set(list_methods)
	for elem in head:
		stemp = stemp.intersection(interpret_head_element(elem, list_methods))
	return stemp


def read_policy(file_name):
        list_rules = []
	policy_map.clear()
	check_file_exists(file_name)
	f = open(file_name, 'r')
        pattern = re.compile('[^\s]+')
	for line in f:
		# comment
		if '#' in line:
			continue
		(t,p1,p2) = extract_rule_head_and_tail(line)
		if t == None:
			continue
		swords = set(pattern.findall(p1))
		swords2 = set(pattern.findall(p2))
		list_rules.append((t,swords,swords2))
	return list_rules
	
def read_policy_single_perm(file_name):
        list_rules = []
	policy_map.clear()
	check_file_exists(file_name)
	f = open(file_name, 'r')
        pattern = re.compile('[^\s]+')
	for line in f:	
		(t,p1,p2) = extract_rule_head_and_tail(line)
		if t == None:
			continue
		lwords = pattern.findall(p1)
		lwords2 = pattern.findall(p2)
		if len(lwords) == 1 and len(lwords2) == 1:
			perm =lwords2[0]
			if perm[0] == '~':
				context = lwords[0]
				perm = perm[1:len(perm)]
				list_rules.append(context+'#'+perm)

	return list_rules



def read_policy2(file_name):
	policy_map.clear()
	check_file_exists(file_name)
	f = open(file_name, 'r')
        pattern = re.compile('[^\s]+')
	for line in f:	
                key = ''
                tag_set = set()	
		lwords = pattern.findall(line)
		for word in lwords:
			if(word[len(word)-1] == ':'):
				key = word[0:len(word)-1]

			else:
				tag_set.add(word)

		if key == '':
			sys.exit('Policy format invalid')
		
		policy_map[key] = tag_set

def print_stats(analysis_time, policy_time):
	print '============================'
	print 'APK file: ',file_name
	print 'Analysis time: ', analysis_time

	if policy_time is not None: 
		print 'Policy checking time: ', policy_time
		print 'Number of rules: ', len(satisfied_rules)
		print 'Number of valid rules: ', satisfied_rules.count('Y')
		print 'Number of violated rules: ', satisfied_rules.count('N')

	print 'Number of methods: ', number_methods
	print '============================'

def print_stats_as_table():
	print file_name, '& ', round(verif_time,2), '& ', check_time ,'& ', number_methods, '& ', ' & '.join(satisfied_rules), '\\'

def print_stats_as_table_in_file(file_n):
	f = open(file_n, 'a')
	new_values = [' ' if x =='Y' else '\\ding{55}' for x in satisfied_rules]
	if f is None:
		sys.exit('Can\'t open file '+file_n)
	line = file_name +' & '+ str(round(verif_time,2)) +' & '+ str(round(check_time,2))+ ' & '+ str(round(ratio,2))+ ' & ' + str(round(pol_check_time,2))+' & ' + str(number_methods)+ ' & ' + ' & '.join(new_values) + ' \\\\'			 
	f.write(line+'\n')
	f.close()	

def print_stats_as_table_in_file2(file_n):
	f = open(file_n, 'a')
	new_values = [' ' if x =='Y' else '\\ding{55}' for x in satisfied_rules]
	if f is None:
		sys.exit('Can\'t open file '+file_n)
	line = file_name + ' & ' + ' & '.join(new_values) + ' \\\\'			 
	f.write(line+'\n')
	f.close()	


###########################################################################################
# fix point computation for the monitor conformance analysis
###########################################################################################

def MonitorConformanceAnalysis(TransSys, monitor):
	analysis_map = {}

	# initialization phase
	all_locs = []
	for loc in TransSys.LocToSucc :
		analysis_map[loc] = set([EVICHECK_INIT_STATE])
		if loc not in all_locs:
			all_locs.append(loc)
		for succ_loc in TransSys.LocToSucc[loc]:
			analysis_map[succ_loc] = set([EVICHECK_INIT_STATE])
			if succ_loc not in all_locs:
				all_locs.append(succ_loc)

			
	init_loc = TransSys.initLoc
	work_list = []
	if (TransSys.initLoc != None):	
		work_list.append(init_loc)
	else:
		work_list = all_locs
		
		
	while len(work_list) > 0:
		print work_list
		current_loc = work_list[0]
		work_list.pop(0)
		print work_list
		set_succ = TransSys.LocToSucc[current_loc]
		for loc in set_succ:
			#prev_set_tmp = analysis_map[loc]
			#print 'CURRENT: ', current_loc
			list_trans_tmp = TransSys.TransToLabels[(current_loc, loc)]
			new_set_tmp = monitor.ComputeSetSuccForBlock(analysis_map[current_loc], list_trans_tmp)
                        new_set_tmp = new_set_tmp.union(analysis_map[loc])
			if(len(new_set_tmp) > len(analysis_map[loc])):
				analysis_map[loc] = new_set_tmp
				if current_loc not in work_list:
					work_list.append(loc)
					

	print analysis_map
	

###########################################################################################
# Return a function based on list of key words given as parameters
###########################################################################################

def GetFuncForKeyWords(apk_file_name, keyword_set):
	set_global_vars(apk_file_name)
	method_set = set()
	for method_id in all_methods:
		for keyword in keyword_set:
			#if keyword in method_id and ('bouncycastle' in method_id or 'javax' in method_id):
			if keyword in method_id:
				method_set.add(method_id)
	return method_set


###########################################################################################
# Just to test the monitor approach
###########################################################################################

def test_monitor():
	
	args = parseargs()
	if args.keep_api:
		KEEP_API = 1
	
	file_name = args.file
	set_global_vars(args.file)
	extract_components_and_methods_info(_a)
	init_api_to_permission()	
	set_global_vars4(args.file)
	trans_table = {}
	trans_table[(EVICHECK_INIT_STATE,'RECORD_AUDIO')] = 1
        actions = ['RECORD_AUDIO']
	my_monitor = Monitor(trans_table, actions, 1)
	
	for trans_sys in methodToTransSys:
		MonitorConformanceAnalysis(methodToTransSys[trans_sys], my_monitor)

	return


###########################################################################################
# Some Data flow analysis with respect to Log 
###########################################################################################

def TestLogDataFlow():
	args = parseargs()
	apk_name = args.file
	a, d, x = AnalyzeAPK(apk_name)
	#show_Permissions(x)
	#p = x.get_permissions( [] )
	#z = p["INTERNET"][0]
	#print z.get_method().get_class_name(), z.get_method().get_name(), z.get_method().get_descriptor()
	#print z 
	#print p
	#detect_Socket_use(x)
	detect_Log(x)
	#detect_MediaRecorder_Video_capture(x)

def detect_Socket_use(x) :
	"""
		@param x : a VMAnalysis instance
		
		@rtype : a list of formatted strings
	"""
	formatted_str = []
	
	structural_analysis_results = x.tainted_packages.search_methods("Ljava/net/Socket","<init>", ".")
	print len(structural_analysis_results)
	for result in xrange(len(structural_analysis_results)) :
		registers = data_flow_analysis(structural_analysis_results, result, x)
		print registers
	



# -- Log  -- #
def detect_Log(x) :
	"""
		@param x : a VMAnalysis instance
		
		@rtype : a list of formatted strings
	"""	
	formatted_str = []
	
	structural_analysis_results = x.tainted_packages.search_methods("Landroid/util/Log","e", ".")	
	
	for result in xrange(len(structural_analysis_results)) :
		registers = data_flow_analysis(structural_analysis_results, result, x)	
		
		if len(registers) > 0 :
			log_msg	= get_register_value(1, registers) 
			
			
			local_formatted_str = "LOG MESSAGE DETECTED: '%s'" % log_msg
			print local_formatted_str 
			#if not(local_formatted_str in formatted_str) :
				#formatted_str.append(local_formatted_str)
	

	#return formatted_str



# -- Video Record -- #
def detect_MediaRecorder_Video_capture(x) :
	"""
		@param x : a VMAnalysis instance
		
		@rtype : a list of formatted strings
	"""	
	formatted_str = []
	
	structural_analysis_results = x.tainted_packages.search_methods("Landroid/media/MediaRecorder","setVideoSource", ".")	
	
	for result in xrange(len(structural_analysis_results)) :
		registers = data_flow_analysis(structural_analysis_results, result, x)	
		
		if len(registers) > 0 :
			video_source_int 	= int(get_register_value(1, registers)) # 1 is the index of the PARAMETER called in the method
			video_source_name 	= 'source' #get_constants_name_from_value(MediaRecorder_VideoSource, video_source_int)
			
			local_formatted_str = "This application captures video from the '%s' source" % video_source_name
			if not(local_formatted_str in formatted_str) :
				formatted_str.append(local_formatted_str)
	

	return formatted_str

	

def detect_Socket_use2(x) :
	"""
		@param x : a VMAnalysis instance
		
		@rtype : a list of formatted strings
	"""
	formatted_str = []
	
	structural_analysis_results = x.tainted_packages.search_methods("Ljava/net/Socket","<init>", ".")
	
	for result in xrange(len(structural_analysis_results)) :
		registers = data_flow_analysis(structural_analysis_results, result, x)

		if len(registers) >= 2 :
			remote_address 	= get_register_value(1, registers) # 1 is the index of the PARAMETER called in the method
			remote_port		= get_register_value(2, registers)
			
			local_formatted_str = "This application opens a Socket and connects it to the remote address '%s' on the '%s' port " % (remote_address, remote_port)
			if not(local_formatted_str in formatted_str) :
				formatted_str.append(local_formatted_str)		
	
	return formatted_str




###########################################################################################

###########################################################################################


def set_global_using_soot(soot_call_graph):
	for caller, callees in soot_call_graph.iteritems():	
		c_name = extract_class_name_from_soot_method(caller)
		c_name = c_name.replace(".","/")
		method_name =  extract_method_name_from_soot_method(caller)  
		method_id = c_name+'->'+method_name
		descriptor = extract_descriptor_from_soot_method(caller)
		method_id = 'L' + method_id + descriptor
		if(method_name == "onClick"):
		      onclick_methods.add(method_id)
		      add_method_with_type_to_global_map('EVICHECK_ONCLICK_HANDLER', method_id)
		if(method_name == "onTouch"):
		      ontouch_methods.add(method_id)		      
		      add_method_with_type_to_global_map('EVICHECK_ONTOUCH_HANDLER', method_id)	      
		if(method_name == "doInBackground"):
		      ontouch_methods.add(method_id)		      
		      add_method_with_type_to_global_map('EVICHECK_DO_INBACKGROUND', method_id)

		if c_name in class_to_methods:
		      class_to_methods[c_name].add(method_id)
		else:
		      set_tmp = set()
		      set_tmp.add(method_id)
		      class_to_methods[c_name] = set_tmp


		called = set()
		for callee in callees:
		      m_name = extract_method_name_from_soot_method(callee)  
		      m_class = extract_class_name_from_soot_method(callee) 
		      m_class = m_class.replace(".","/")
		      m_desc = extract_descriptor_from_soot_method(callee)

		      if(m_name != '' and m_class != ''):
				    m_name = 'L' + m_class +'->'+m_name + m_desc;			     
				    called.add(m_name)	
				    
				    if m_class in class_to_methods:
					    class_to_methods[m_class].add(m_name)
				    else:
					    set_tmp = set()
					    set_tmp.add(m_name)
					    class_to_methods[m_class] = set_tmp
		      else: 
                             #print 'not found in ', _str
			      continue
                            
		      if m_name in called_by:
                              called_by[m_name].add(method_id)
		      else: 
                              set_tmp = set()
                              set_tmp.add(method_id)
                              called_by[m_name] = set_tmp
                            
		      if method_id in call_graph:
                              call_graph[method_id].add(m_name)
		      else:
                              set_tmp = set()
			      set_tmp.add(m_name)                               
                              call_graph[method_id] = set_tmp

		      all_methods.add(m_name)

		      all_methods.add(method_id)
	# entry points are not called by any other methods
	for method in all_methods:
		
		#if method not in called_by and (method != 'LdummyMainClass->dummyMainMethod()V'):
		if method in called_by:
			method_called_by =  called_by[method]
			if ('LdummyMainClass->dummyMainMethod()V' in method_called_by):
				entry_points.add(method)
			
	

def transform_from_soot_to_evicheck_method(method):
	class_name =  extract_class_name_from_soot_method(method)
	class_name = class_name.replace(".","/")
	method_name = extract_method_name_from_soot_method(method)
	descriptor = extract_descriptor_from_soot_method(method)
	return (class_name+'->'+method_name+descriptor)


def extract_class_name_from_soot_method(method):
	_match = re.search(r'(<)((\W|\w)+)(:)', method)
	if(_match):                             
		return _match.group(2)			                                    
	else: 	
                	
		return ''
	return


def extract_method_name_from_soot_method(method):
	_match = re.search(r'(:\s)((\W|\w)+)(\()', method)
	if(_match):                             
		return _match.group(2)			                                    
	else: 	
                	
		return ''
	return


def extract_descriptor_from_soot_method(method):
	_match = re.search(r'(\((\W|\w)+)(>)', method)
	if(_match): 
		desc = _match.group(1)
		if desc[len(desc)-1] == ';':
		      desc = desc[0:len(desc)-1]
		return desc			                                    
	else: 	
                	
		return ''
	return



def extract_solution_from_sat4j(answer):
	_match = re.search(r'(solution\(s\)\nv)((\W|\w)+)(\nc\ objective)', answer)
	if(_match): 
		return _match.group(2)			                                   
	else: 	
		
		return None



def extract_solution_from_z3(answer):
	pattern = re.compile(r'(.*)(\(objectives.*)(\(model.*)', re.DOTALL)
	_match = pattern.search(answer)
	if(_match): 
		if 'unsat' not in _match.group(1):
			return _match.group(3)
		else:
			return None				                                   
	else: 			
		return None




def PrintMethodsIfCalledAndContainText(search_text, call_graph):

	for caller, callees in call_graph.iteritems():
		list_tmp = set([s for s in callees if search_text in s])
		if len(list_tmp) > 0:
			return caller , list_tmp
	return None, None



###########################################################################################

###########################################################################################

def print_stats_as_table_in_file(file_n, file_name, verif_time, check_time, pol_check_time, number_methods, satisfied_rules):
	f = open(file_n, 'a')
	new_values = [' ' if x =='Y' else '\\ding{55}' for x in satisfied_rules]
	if f is None:
		sys.exit('Can\'t open file '+file_n)
	line = file_name +' & '+ str(round(verif_time,2)) +' & '+ str(round(check_time,2))+ ' & ' + str(round(pol_check_time,2))+' & ' + str(number_methods)+ ' & ' + ' & '.join(satisfied_rules) + ' \\\\'			 
	f.write(line+'\n')
	f.close()	


def GenSpec(args):
	global tag_map
	global call_graph
	global called_by
	global file_name
	
	if  args.file is None:
		print 'APK file is missing'
		return

	if  args.policy is None:
		print 'Policy file is missing'
		return
	
	if  args.res_file is None:
		print 'Result file is missing'
		return
	

	w_time = time.time()
	_a = apk.APK(args.file)
	file_name = args.file	
	set_global_vars(args.file)	
	extract_components_and_methods_info(_a)		
	init_api_to_permission()
	generate_init_map_from_permissions(all_methods)	

	my_time	= time.time()	        
	gen_certificate() 		
	verif_time = time.time() - my_time
	
	pol_check_time = 0
	if args.policy is not None:
		my_time = time.time()
		check_policy(args.policy)
		my_time = time.time() - my_time
		pol_check_time = my_time

	w_time = time.time() - w_time
	my_time = time.time()
	check_certificate()
	check_time = time.time() - my_time
	number_methods = len(tag_map)

	print_stats_as_table_in_file(args.res_file, file_name, verif_time, check_time, pol_check_time, number_methods, satisfied_rules)

		
def GenerateSuccessors(method, permissions, my_call_graph, my_tag_map):
	list_res = []
	if method not in my_call_graph:
		return list_res
	
	s_succ = set([s for s in my_call_graph[method]])
	perms = set([p for p in permissions])
	
	for s in s_succ:
		common_perms = perms.intersection(my_tag_map[s])
		if len(common_perms) > 0:
			list_res.append((s, common_perms))
			perms.difference_update(common_perms)
		
		if len(perms) == 0:
			break
	
	assert len(perms) == 0
	return list_res


def ExtractCurrentPath(working_stack, mark):
	
	res_path = [(m[0],m[1]) for m in reversed(working_stack) if m[2] == mark]
	return res_path
	

def ComputeCallChainFromMethodToAPI(target_method, relevant_permissions, my_call_graph, my_tag_map):
	assert target_method in my_tag_map
	assert target_method in my_call_graph	
	assert my_tag_map[target_method].issuperset(relevant_permissions)
	list_paths = []	
       		
	marked = 1
	unmarked = 0
	my_working_stack = []	
	current_method = target_method
	my_working_stack.insert(0, (current_method, relevant_permissions, unmarked))


	while (len(my_working_stack) > 0):
		current_method , permissions, current_mark = my_working_stack.pop(0)
		
		if current_mark == unmarked:
			my_working_stack.insert(0, (current_method, permissions, marked))
			s_succ = GenerateSuccessors(current_method, permissions, my_call_graph, my_tag_map)

			if len(s_succ) == 0: 
				assert len(permissions) > 0
				current_path = ExtractCurrentPath(my_working_stack,  marked)
				list_paths.append(current_path)
			else:
				
				for s in s_succ: 
					m_tmp , perms_tmp = s 
					my_working_stack.insert(0, (m_tmp, perms_tmp, unmarked))
		
				



	print list_paths




###########################################################################################
# Takes an API spec as argument an return the corresponding permission spec
###########################################################################################

def Transform_APISpec_PERMSpec(api_spec):
        res_spec = {}
        for f, s in api_spec.iteritems():
                new_spec = {}
                for context, apis in s.iteritems():
                        perms = set([api_to_permission[extract_method_fullname_without_return(a)] for a in apis])
                        new_spec[context] = perms
                
                res_spec[f] = new_spec
        return res_spec
                

def Test_Transform_APISpec_PERMSpec(spec_file):
        init_api_to_permission()
        copy_tag_map_and_take_return_intoaccount(TAG_TO_PARMISSION, api_to_permission, all_methods)
        spec = read_spec_file_for_methods(spec_file)
        new_spec = Transform_APISpec_PERMSpec(spec)
        
        for f_name, spec in new_spec.iteritems():
                
                PrintTypeToTagMap_To_File_in_append_mode2(spec_file+"_transformed", f_name, spec)
        print new_spec



###########################################################################################

###########################################################################################



my_time = 0

def main():

        
        
        
        
        



        '''
	with open ("tmp", "r") as myfile:
		sol=myfile.read()
		print sol 
		
	
		res = extract_solution_from_z3(sol)
		res = get_vars_in_z3_sol(res)
		print res
	return
	'''
        global verif_time
	global check_time
	global pol_check_time
	global number_methods
	global file_name
	global ratio
	
	
	args = parseargs()


	if args.test_pol_spec:		
		if (args.policy is not None) and (args.spec_file is not None):
			if args.api:
				pol = read_policy_single_perm(args.policy)
				map_spec = read_spec_file2(args.spec_file)
				test_policy_for_spec(pol, map_spec)
				return

			pol = read_policy_single_perm(args.policy)
			map_spec = read_spec_file2(args.spec_file)
			test_policy_for_spec(pol, map_spec)			
			return		

	#if (args.spec_file is not None)and (args.pb_solution is not None):
	#	map_back_result_from_pbs(args.spec_file, '', args.pb_solution)
	#	return

        
	if args.spec_file is not None:
                #CountPERMSInSpecs(args.spec_file)
                #return
                #CountApiInSpecs(args.spec_file)
                #return
                #Test_Transform_APISpec_PERMSpec(args.spec_file)
                #return
		#generate_whole_pb_problem2(args.spec_file, "")
		if args.z3:
			if  args.policy is not None and args.api:
				generate_whole_pb_problem_z3_api(args.spec_file, args.policy)	                                
                                #generate_whole_pb_problem_z3_api_iter(args.spec_file, args.policy)	
				return

			if args.policy is  not None:
				generate_whole_pb_problem_z3(args.spec_file, args.policy)
			return
		
		if args.policy is  not None:
			generate_whole_pb_problem_with_numb_rules(args.spec_file, "",50, args.policy)
		else:
			generate_whole_pb_problem_with_numb_rules2(args.spec_file, "",50)
		return

	if (args.file is not None):
		if not os.path.isfile(args.file):
			print '\nCan\'t find file: '+args.file+'\n'
			sys.exit(0)
	else:
		sys.exit(0)
	

	_a = apk.APK(args.file)

	file_name = args.file

	if(args.soot):			
		CALL_GRAPH_FROM_SOOT = call_soot(args.file)				
		set_global_using_soot(CALL_GRAPH_FROM_SOOT)		
		extract_components_and_methods_info(_a)
		init_api_to_permission_for_soot()
	else:
		set_global_vars(args.file)
		extract_components_and_methods_info(_a)
		init_api_to_permission()				
		copy_tag_map_and_take_return_intoaccount(TAG_TO_PARMISSION, api_to_permission, all_methods)

                
        if args.ext_map is not None:
                ExtendApiToPermission(api_to_permission, args.ext_map)
                                
	if args.check:	
		if args.cert is None:
			sys.exit('\nPlease provide a certificate file!')
		read_certificate(args.cert)
		#print len(tag_map)
		#return
		my_time = time.time()
		check_certificate()
		my_time = time.time() - my_time
		verif_time = my_time
		
		pol_check_time = None
		if args.policy is not None:
			my_time = time.time()
			check_policy(args.policy)
			my_time = time.time() - my_time
			pol_check_time = my_time
		

		number_methods = len(tag_map)	
		print_stats(verif_time, pol_check_time)		
		return
		
	elif args.gen:	
		
		if args.init is not None:
			generate_default_init_map_from_file(all_methods,args.init)
		elif args.perm:			
			generate_init_map_from_permissions(all_methods)			       	       
			copy_content_for_entries(all_methods, api_to_permission, tag_map)	      				
		else:
			generate_default_init_map(all_methods)

			
		my_time	= time.time()	        
		gen_certificate() 
		my_time = time.time() - my_time
		verif_time = my_time
	
		if args.infer_spec is not None:			
			mp_tmp = GenerateTypeToTagMap()
			print mp_tmp
			#PrintTypeToTagMap_To_File(args.infer_spec, mp_tmp)
			PrintTypeToTagMap_To_File_in_append_mode(args.infer_spec, mp_tmp)
		pol_check_time = None
		if args.policy is not None:
			my_time = time.time()
			check_policy(args.policy)
			my_time = time.time() - my_time
			pol_check_time = my_time
		
		
			
			
		if args.cert is not None:
			print_certificate(args.cert)

		elif args.entry is not None:
			print_certificate_for_entry_points(args.entry)

		number_methods = len(tag_map)	
		print_stats(verif_time, pol_check_time)	

		if args.counterexample:
			#ComputeCallChainFromMethodToAPI('Lcom/whatsapp/VerifySms->onResume()V', set(['SEND_SMS']), call_graph, tag_map)
                        ComputeCallChainFromMethodToAPI('Landroid/support/v4/print/PrintHelperKitkat$2$1->doInBackground([Ljava/lang/Object;)Ljava/lang/Object', set(['READ_CONTACTS']), call_graph, tag_map)
			#ComputeCallChainFromMethodToAPI('Lcom/dipak/audiorecording/AudioRecordingActivity->onCreate(Landroid/os/Bundle;)V', set(['RECORD_AUDIO']), call_graph, tag_map)

		
	elif args.gencheck:

		GenSpec(args)
		return
		if args.init is not None:
			generate_default_init_map_from_file(all_methods,args.init)
		elif args.perm:			
			generate_init_map_from_permissions(all_methods)			       	       
			copy_content_for_entries(all_methods, api_to_permission, tag_map)	      				
		else:
			generate_default_init_map(all_methods)

			
		my_time	= time.time()	        
		gen_certificate() 
		my_time = time.time() - my_time
		verif_time = my_time

		if args.policy is not None:
			my_time = time.time()
			check_policy(args.policy)
			my_time = time.time() - my_time
			pol_check_time = my_time
		
		my_time = time.time()
		check_certificate()
		my_time = time.time() - my_time
		check_time = my_time

		print_stats(check_time, pol_check_time)
                
		
	elif args.list:	
		#res_tmp = PrintMethodsIfCalledAndContainText('ClipboardManager->setText', call_graph)
		#res_tmp = PrintMethodsIfCalledAndContainText('loadUrl', call_graph)
		#res_tmp = PrintMethodsIfCalledAndContainText('set', call_graph)
		#print res_tmp
		#return
		print_call_graph()


	return

       
      




if __name__ == "__main__":
	main()
