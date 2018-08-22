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
from TransitionSystem import *
from Monitor import *
from just_for_test import *
from FromAndroWarn import *


import sys
import os
import base64
import pprint
import datetime
import argparse
import re
import time


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
	parser.add_argument("-f", "--file", help="APK File to check", type=str, required=True)
        parser.add_argument("-t", "--cert", help="certificate file", type=str, required=False)
	parser.add_argument("-pb", "--pb_solution", help="read solution of the pseudo boolean solver sat4j", type=str, required=False)
	parser.add_argument("-e", "--entry", help="certificate restricted to entry points", type=str, required=False)
	parser.add_argument("-i", "--init", help="initial tag map", type=str, required=False)
	parser.add_argument("-m", "--perm", help="use permissions as initial tag map", action = "store_true", required=False)
        parser.add_argument("-l", "--list", help="display the list of methods in the APK file showing call relations", action = "store_true", required=False)
	parser.add_argument("-s", "--spec_file", help="read specification file", type=str, required=False)
	parser.add_argument("-p", "--policy", help="policy to check", type=str, required=False)
	parser.add_argument("-c", "--check", help="check certificate", action = "store_true", required=False)
	parser.add_argument("-g", "--gen", help="generate certificate", action = "store_true", required=False)	
	parser.add_argument("-k", "--keep_api", help="use api functions instead of permissions in trace monitoring", action = "store_true", required=False)
	parser.add_argument("-r", "--infer_spec", help="infer specification", type=str, required=False)
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
	init_api_to_permission()
	
	for method in all_methods:

		# in androguard permission map the return value is not included in the method description
		new_name = extract_method_fullname_without_return(method)
		if new_name in api_to_permission and new_name != method:
			api_to_permission[method] = api_to_permission[new_name]
			del api_to_permission[new_name]


	for key in method_set:
		if key in api_to_permission.keys():
			settmp = set()
			settmp.add(api_to_permission[key])
			tag_map[key] = settmp 
		else:
			tag_map[key] = set()

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
		if method not in called_by:
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
		      ontouch_methods.add(method_id)		      
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
				#print 'tag_map_callee', tag_map[callee]
				tag_set2 = tag_set2.union(tag_map[callee])
			res = tag_set.symmetric_difference(tag_set2)	
			if len(res) > 0:        
				#print res
				#print tag_set
				#print tag_set2
			
				print '\n\nInvalid certificate! Problem located in method: ' + key + '\n\n'
				return
				
	print '\n\nCertificate is valid\n\n'	 



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
				
	print '\n\nCertificate is valid\n\n'
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
				
	print '\n\nCertificate is valid\n\n'	 


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




	
def read_spec_file2(f_name):	
	
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
	
	

def read_res_from_pbs(f_name):
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



###########################################################################################

###########################################################################################	

def read_certificate(file_name):
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
									print 'Rule', rule_num, ' ==> ', rule_head,':',rule_tail
									print 'Policy violated! Tag '+ tag[1:len(tag)] +' is in '+ entry+'\n'
									exit_loop = 1
									policy_violated = 1
									rule_violated = 1
									break
								
						else:
							if tag not in tag_map[entry]:
								print 'Rule', rule_num, ' ==> ', rule_head,':',rule_tail
								print 'Policy violated! Tag '+ tag +' is not in '+ entry+'\n'
								exit_loop = 1
								policy_violated = 1
								rule_violated = 1
								break
									
					if exit_loop == 1: break
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
						print 'Rule', rule_num, ' ==> ', rule_head,':V',rule_tail
						print 'Policy violated!\n'
						policy_violated = 1
						rule_violated = 1
						break
			if rule_violated == 0:
				satisfied_rules.append('Y')
			else:
				satisfied_rules.append('N')
					
	if policy_violated == 0:
		print '\nPolicy satisfied!'
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


def PrintTypeToTagMap_To_File(file_n, type_to_tag_map):	
	f = open(file_n, 'a')
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
	f = open(file_name, 'r')
        pattern = re.compile('[^\s]+')
	for line in f:	
		(t,p1,p2) = extract_rule_head_and_tail(line)
		if t == None:
			continue
		swords = set(pattern.findall(p1))
		swords2 = set(pattern.findall(p2))
		list_rules.append((t,swords,swords2))
	return list_rules
	


def read_policy2(file_name):
	policy_map.clear()
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


my_time = 0

def main():

        global verif_time
	global check_time
	global pol_check_time
	global number_methods
	global file_name
	global ratio
        #print DVM_PERMISSIONS_BY_ELEMENT.keys()
	#return
	#key_words = set(['SecureRandom->', 'SecretKeySpec->', 'SecretKeySpec->', 'Cipher->', 'IvParameterSpec'])
	args = parseargs()
	#set_functions = GetFuncForKeyWords(args.file, key_words)
	#if(len(set_functions) > 0):
	#	print 'File:', args.file, '    Contains:', set_functions
	#print '\n\n\n*********************************************************************************\n\n\n'
	#just_for_test_conjunctive_rules(args.spec_file)
	#return



	#TestLogDataFlow()
	#return

	#key_words = set(['Landroid/util/Log'])
	#args = parseargs()
	#set_functions = GetFuncForKeyWords(args.file, key_words)
	#if(len(set_functions) > 0):
	#	print 'File:', args.file, '    Contains:', set_functions
	#else:
	#	print 'NOLOG'
	
	#print '\n\n\n*********************************************************************************\n\n\n'
	#just_for_test_conjunctive_rules(args.spec_file)
	#return


	#my_spec = read_spec_file(args.spec_file)
	#generate_whole_pb_problem2(args.spec_file,'permissive2')
	#generate_whole_pb_problem(args.spec_file,'')
	#generate_pb_problem(my_spec,'<=')
	#sys.exit('')
	
	#just_for_test(args.spec_file)
	#sys.exit('')


	#read_res_from_pbs(args.pb_solution)
	#map_back_result_from_pbs(args.spec_file, '', args.pb_solution)
	#sys.exit('')

	_a = apk.APK(args.file)
	#print _a.get_android_manifest_axml().get_xml()
	#return

	#print _a.get_activities()
	#print _a.get_services()
	#print _a.get_receivers()
	#print _a.get_libraries()
	#return
	#return
	#extract_components_and_methods_info(_a)
	
	#a = 'abababab'
	#print a.replace('a','c')
	#print a
	#return
	#_a.show()
	#for a in get_main_activities(_a):
	#	print a
	#print get_main_activities(_a)
	#print _a.get_signature_name()
	#print _a.get_package()
	#return
	#print("Analyse file: {:s}".format(args.file))
	#print("Package name: {:s}".format(_a.get_package()))
	#set_global_vars(args.file)	
	file_name = args.file
	#set_global_vars2(args.file)
	#return
	
	#set_global_vars2(args.file)
	#return
	
	set_global_vars(args.file)
	extract_components_and_methods_info(_a)	
	init_api_to_permission()

	if args.check:	
		if args.cert is None:
			sys.exit('Please provide an *.evi file!')
		read_certificate(args.cert)
		my_time = time.time()
		check_certificate()
		my_time = time.time() - my_time
		verif_time = my_time
		#print 'Time:', my_time
		#print len(tag_map)
		
		if args.policy is not None:
			check_policy(args.policy)
			
		return
		my_time = time.time() - my_time
		print 'Time:', my_time
		return
	elif args.gen:		
		if args.init is not None:
			generate_default_init_map_from_file(all_methods,args.init)
		elif args.perm:
			generate_init_map_from_permissions(all_methods)			
		else:
			generate_default_init_map(all_methods)

			 
		my_time	= time.time()
	        
		gen_certificate() 

		my_time = time.time() - my_time
		verif_time = my_time
	
		if args.infer_spec is not None:			
			mp_tmp = GenerateTypeToTagMap()
			print mp_tmp
			PrintTypeToTagMap_To_File(args.infer_spec, mp_tmp)

		
		
		#print 'Time:', my_time
	
		#print_certificate2()
		
		#print_certificate('certtttt')
		#return
		#print_certificate()
		#return
		if args.policy is not None:
			my_time = time.time()
			check_policy(args.policy)
			my_time = time.time() - my_time
			pol_check_time = my_time
			#print 'File:', args.file
			#print 'Satisfied rules: ', ' & '.join(satisfied_rules)
			#print 'Time: ', verif_time
			#print 'Numbre of functions:', len(tag_map)			
			number_methods = len(tag_map)
			
			
		if args.cert is not None:
			print_certificate(args.cert)
		elif args.entry is not None:
			print_certificate_for_entry_points(args.entry)


		#################################################
			# just for the experiments purpose
		my_time = time.time()
		check_certificate2()
		my_time = time.time() - my_time
		check_time = my_time
		ratio = verif_time / check_time
		print_stats_as_table()
		print_stats_as_table_in_file("res7.tab")
		#################################################

		return
		

                my_time = time.time() - my_time
		print 'Time:', my_time
		print 'Numbre of functions:', len(tag_map)
		return
		print_certificate()
	elif args.list:		
		print_call_graph()
		

	#pretty_print_certificate()
	#return;
	#set_global_vars(args.file)
		
        #generate_init_map(all_methods) 
	
	#gen_certificate()   
	
	#check_certificate()

	#print_certificate()
	#pretty_print_certificate()
	#print_call_graph()
	


	return

       
      




if __name__ == "__main__":
	main()
