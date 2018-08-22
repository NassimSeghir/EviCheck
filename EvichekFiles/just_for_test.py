
#######################################################################################################################

# Copyright (C) 2014, Mohamed Nassim Seghir (mseghir@inf.ed.ac.uk) and David Aspinall (David.Aspinall@ed.ac.uk)
# All rights reserved.

#######################################################################################################################



from EviCheck_backup import read_spec_file
from EviCheck_backup import read_spec_file2
from EviCheck_backup import generate_whole_pb_problem3
from EviCheck_backup import generate_whole_pb_problem4
from EviCheck_backup import extract_context_permission_for_set, extract_context_permission_as_pairs_for_set, extract_perm_to_context_for_set

from EviCheck import var_rename,  var_rename_back
 



def test_policy_for_spec(policy, map_spec):
        
	policy_pairs =   extract_context_permission_as_pairs_for_set(policy)	
		
	counter = 0
	print '\n\n'
	for apk_name, spec in map_spec.iteritems():
		pairs_from_spec =  extract_context_permission_as_pairs_for_set(spec)
		intersect_pairs = policy_pairs.intersection(pairs_from_spec)
		if len(intersect_pairs) > 0:
			counter = counter + 1
			print 'policy violated by: '+apk_name
		


	print '\n\nPolicy violated by '+ str(counter) + ' apps from ' + str(len(map_spec)) 
        print var_rename


def just_for_test(f_name):

	policy2 = set(['EVICHECK_RECEIVER_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_ACTIVITY_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_DESTROY_METHOD#GET_ACCOUNTS', 'EVICHECK_RECEIVER_METHOD#SEND_SMS', 'EVICHECK_ONTOUCH_HANDLER#ACCESS_COARSE_LOCATION', 'EVICHECK_ONCLICK_HANDLER#ACCESS_COARSE_LOCATION', 'EVICHECK_RESTART_METHOD#READ_PHONE_STATE', 'EVICHECK_SERVICE_METHOD#SEND_SMS', 'EVICHECK_ONCLICK_HANDLER#BROADCAST_STICKY', 'EVICHECK_ONTOUCH_HANDLER#GET_TASKS', 'EVICHECK_SERVICE_METHOD#ACCESS_COARSE_LOCATION', 'EVICHECK_ONCLICK_HANDLER#KILL_BACKGROUND_PROCESSES', 'EVICHECK_RESTART_METHOD#VIBRATE', 'EVICHECK_SERVICE_METHOD#BLUETOOTH_ADMIN', 'EVICHECK_RESUME_METHOD#READ_HISTORY_BOOKMARKS', 'EVICHECK_ACTIVITY_METHOD#SEND_SMS', 'EVICHECK_RECEIVER_METHOD#CAMERA', 'EVICHECK_START_METHOD#AUTHENTICATE_ACCOUNTS', 'EVICHECK_ONCREATE_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_ACTIVITY_METHOD#EXPAND_STATUS_BAR', 'EVICHECK_SERVICE_METHOD#NFC', 'EVICHECK_RECEIVER_METHOD#WRITE_SETTINGS', 'EVICHECK_PAUSE_METHOD#RESTART_PACKAGES', 'EVICHECK_ONCREATE_METHOD#SET_WALLPAPER', 'EVICHECK_DESTROY_METHOD#READ_LOGS', 'EVICHECK_RECEIVER_METHOD#SET_TIME', 'EVICHECK_DESTROY_METHOD#READ_PHONE_STATE', 'EVICHECK_ONTOUCH_HANDLER#MODIFY_AUDIO_SETTINGS', 'EVICHECK_ONTOUCH_HANDLER#BLUETOOTH', 'EVICHECK_RECEIVER_METHOD#ACCESS_FINE_LOCATION', 'EVICHECK_ONCLICK_HANDLER#READ_HISTORY_BOOKMARKS', 'EVICHECK_ONTOUCH_HANDLER#ACCESS_WIFI_STATE', 'EVICHECK_PAUSE_METHOD#CHANGE_COMPONENT_ENABLED_STATE', 'EVICHECK_DESTROY_METHOD#READ_CONTACTS', 'EVICHECK_SERVICE_METHOD#SET_TIME', 'EVICHECK_RESTART_METHOD#READ_LOGS', 'EVICHECK_ONTOUCH_HANDLER#READ_LOGS', 'EVICHECK_RESUME_METHOD#READ_SYNC_STATS', 'EVICHECK_SERVICE_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_DESTROY_METHOD#VIBRATE', 'EVICHECK_SERVICE_METHOD#WRITE_SECURE_SETTINGS', 'EVICHECK_SERVICE_METHOD#READ_HISTORY_BOOKMARKS', 'EVICHECK_DESTROY_METHOD#RESTART_PACKAGES', 'EVICHECK_SERVICE_METHOD#READ_PHONE_STATE', 'EVICHECK_ONCLICK_HANDLER#SEND_SMS'])

	policy2 = set(['EVICHECK_ACTIVITY_METHOD#READ_SMS', 'EVICHECK_SERVICE_METHOD#NFC', 'EVICHECK_ACTIVITY_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_DESTROY_METHOD#GET_ACCOUNTS', 'EVICHECK_RECEIVER_METHOD#SEND_SMS', 'EVICHECK_ONTOUCH_HANDLER#ACCESS_COARSE_LOCATION', 'EVICHECK_RECEIVER_METHOD#WRITE_SYNC_SETTINGS', 'EVICHECK_ONTOUCH_HANDLER#RECORD_AUDIO', 'EVICHECK_RECEIVER_METHOD#READ_SMS', 'EVICHECK_RESUME_METHOD#DISABLE_KEYGUARD', 'EVICHECK_SERVICE_METHOD#SEND_SMS', 'EVICHECK_ONTOUCH_HANDLER#GET_TASKS', 'EVICHECK_ONCLICK_HANDLER#SET_WALLPAPER', 'EVICHECK_SERVICE_METHOD#RECORD_AUDIO', 'EVICHECK_SERVICE_METHOD#ACCESS_COARSE_LOCATION', 'EVICHECK_SERVICE_METHOD#WRITE_SMS', 'EVICHECK_RECEIVER_METHOD#ACCESS_FINE_LOCATION', 'EVICHECK_ACTIVITY_METHOD#SEND_SMS', 'EVICHECK_RECEIVER_METHOD#CAMERA', 'EVICHECK_RESUME_METHOD#SEND_SMS', 'EVICHECK_ONCREATE_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_SERVICE_METHOD#GET_TASKS', 'EVICHECK_RECEIVER_METHOD#CHANGE_WIFI_STATE', 'EVICHECK_PAUSE_METHOD#RESTART_PACKAGES', 'EVICHECK_ACTIVITY_METHOD#WRITE_SMS', 'EVICHECK_ACTIVITY_METHOD#CHANGE_NETWORK_STATE', 'EVICHECK_ONCREATE_METHOD#SET_WALLPAPER', 'EVICHECK_ONCLICK_HANDLER#WRITE_SMS', 'EVICHECK_DESTROY_METHOD#READ_LOGS', 'EVICHECK_RESUME_METHOD#STATUS_BAR', 'EVICHECK_PAUSE_METHOD#DISABLE_KEYGUARD', 'EVICHECK_START_METHOD#READ_LOGS', 'EVICHECK_RECEIVER_METHOD#SET_WALLPAPER_HINTS', 'EVICHECK_ONCREATE_METHOD#SET_WALLPAPER_HINTS', 'EVICHECK_DESTROY_METHOD#GET_TASKS', 'EVICHECK_SERVICE_METHOD#SET_TIME', 'EVICHECK_SERVICE_METHOD#READ_SMS', 'EVICHECK_SERVICE_METHOD#ACCESS_WIFI_STATE', 'EVICHECK_START_METHOD#CHANGE_WIFI_MULTICAST_STATE', 'EVICHECK_ONTOUCH_HANDLER#READ_LOGS', 'EVICHECK_RESUME_METHOD#READ_SYNC_STATS', 'EVICHECK_PAUSE_METHOD#STATUS_BAR', 'EVICHECK_SERVICE_METHOD#WRITE_SECURE_SETTINGS', 'EVICHECK_SERVICE_METHOD#READ_HISTORY_BOOKMARKS', 'EVICHECK_ONCLICK_HANDLER#SEND_SMS'])
	
	policy2 = set(['EVICHECK_ACTIVITY_METHOD#READ_SMS', 'EVICHECK_SERVICE_METHOD#NFC', 'EVICHECK_ACTIVITY_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_DESTROY_METHOD#GET_ACCOUNTS', 'EVICHECK_RECEIVER_METHOD#SEND_SMS', 'EVICHECK_ONTOUCH_HANDLER#ACCESS_COARSE_LOCATION', 'EVICHECK_RECEIVER_METHOD#WRITE_SYNC_SETTINGS', 'EVICHECK_ONTOUCH_HANDLER#RECORD_AUDIO', 'EVICHECK_RECEIVER_METHOD#READ_SMS', 'EVICHECK_RESUME_METHOD#DISABLE_KEYGUARD', 'EVICHECK_SERVICE_METHOD#SEND_SMS', 'EVICHECK_ONTOUCH_HANDLER#GET_TASKS', 'EVICHECK_ONCLICK_HANDLER#SET_WALLPAPER', 'EVICHECK_SERVICE_METHOD#RECORD_AUDIO', 'EVICHECK_SERVICE_METHOD#ACCESS_COARSE_LOCATION', 'EVICHECK_SERVICE_METHOD#WRITE_SMS', 'EVICHECK_RECEIVER_METHOD#ACCESS_FINE_LOCATION', 'EVICHECK_ACTIVITY_METHOD#SEND_SMS', 'EVICHECK_RECEIVER_METHOD#CAMERA', 'EVICHECK_RESUME_METHOD#SEND_SMS', 'EVICHECK_ONCREATE_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_SERVICE_METHOD#GET_TASKS', 'EVICHECK_RECEIVER_METHOD#CHANGE_WIFI_STATE', 'EVICHECK_PAUSE_METHOD#RESTART_PACKAGES', 'EVICHECK_ACTIVITY_METHOD#WRITE_SMS', 'EVICHECK_ACTIVITY_METHOD#CHANGE_NETWORK_STATE', 'EVICHECK_ONCREATE_METHOD#SET_WALLPAPER', 'EVICHECK_ONCLICK_HANDLER#WRITE_SMS', 'EVICHECK_DESTROY_METHOD#READ_LOGS', 'EVICHECK_RESUME_METHOD#STATUS_BAR', 'EVICHECK_PAUSE_METHOD#DISABLE_KEYGUARD', 'EVICHECK_START_METHOD#READ_LOGS', 'EVICHECK_RECEIVER_METHOD#SET_WALLPAPER_HINTS', 'EVICHECK_ONCREATE_METHOD#SET_WALLPAPER_HINTS', 'EVICHECK_DESTROY_METHOD#GET_TASKS', 'EVICHECK_SERVICE_METHOD#SET_TIME', 'EVICHECK_SERVICE_METHOD#READ_SMS', 'EVICHECK_SERVICE_METHOD#ACCESS_WIFI_STATE', 'EVICHECK_START_METHOD#CHANGE_WIFI_MULTICAST_STATE', 'EVICHECK_ONTOUCH_HANDLER#READ_LOGS', 'EVICHECK_RESUME_METHOD#READ_SYNC_STATS', 'EVICHECK_PAUSE_METHOD#STATUS_BAR', 'EVICHECK_SERVICE_METHOD#WRITE_SECURE_SETTINGS', 'EVICHECK_SERVICE_METHOD#READ_HISTORY_BOOKMARKS', 'EVICHECK_ONCLICK_HANDLER#SEND_SMS'])

	policy=set(['EVICHECK_ACTIVITY_METHOD#READ_SMS', 'EVICHECK_RECEIVER_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_RESUME_METHOD#READ_HISTORY_BOOKMARKS', 'EVICHECK_ACTIVITY_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_DESTROY_METHOD#GET_ACCOUNTS', 'EVICHECK_RECEIVER_METHOD#SEND_SMS', 'EVICHECK_ONTOUCH_HANDLER#ACCESS_COARSE_LOCATION', 'EVICHECK_RESUME_METHOD#RESTART_PACKAGES', 'EVICHECK_RECEIVER_METHOD#WRITE_SYNC_SETTINGS', 'EVICHECK_ONCREATE_METHOD#READ_SMS', 'EVICHECK_ONTOUCH_HANDLER#RECORD_AUDIO', 'EVICHECK_RECEIVER_METHOD#READ_SMS', 'EVICHECK_RESUME_METHOD#DISABLE_KEYGUARD', 'EVICHECK_RESTART_METHOD#RESTART_PACKAGES', 'EVICHECK_ONCREATE_METHOD#SET_WALLPAPER_HINTS', 'EVICHECK_SERVICE_METHOD#SEND_SMS', 'EVICHECK_ONCLICK_HANDLER#BROADCAST_STICKY', 'EVICHECK_ONTOUCH_HANDLER#GET_TASKS', 'EVICHECK_ONCLICK_HANDLER#SET_WALLPAPER', 'EVICHECK_SERVICE_METHOD#RECORD_AUDIO', 'EVICHECK_SERVICE_METHOD#ACCESS_COARSE_LOCATION', 'EVICHECK_SERVICE_METHOD#CHANGE_WIFI_STATE', 'EVICHECK_SERVICE_METHOD#WRITE_SMS', 'EVICHECK_SERVICE_METHOD#BLUETOOTH_ADMIN', 'EVICHECK_RECEIVER_METHOD#ACCESS_FINE_LOCATION', 'EVICHECK_ACTIVITY_METHOD#SEND_SMS', 'EVICHECK_RECEIVER_METHOD#CAMERA', 'EVICHECK_RESUME_METHOD#SEND_SMS', 'EVICHECK_START_METHOD#AUTHENTICATE_ACCOUNTS', 'EVICHECK_ONCREATE_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_SERVICE_METHOD#GET_TASKS', 'EVICHECK_ACTIVITY_METHOD#EXPAND_STATUS_BAR', 'EVICHECK_RECEIVER_METHOD#CHANGE_WIFI_STATE', 'EVICHECK_ONCLICK_HANDLER#READ_HISTORY_BOOKMARKS', 'EVICHECK_SERVICE_METHOD#WRITE_SECURE_SETTINGS', 'EVICHECK_ONCREATE_METHOD#SEND_SMS', 'EVICHECK_PAUSE_METHOD#RESTART_PACKAGES', 'EVICHECK_ACTIVITY_METHOD#WRITE_SMS', 'EVICHECK_ACTIVITY_METHOD#CHANGE_NETWORK_STATE', 'EVICHECK_ONCREATE_METHOD#SET_WALLPAPER', 'EVICHECK_ONCLICK_HANDLER#WRITE_SMS', 'EVICHECK_RESTART_METHOD#GET_TASKS', 'EVICHECK_RECEIVER_METHOD#SET_TIME', 'EVICHECK_RESUME_METHOD#STATUS_BAR', 'EVICHECK_PAUSE_METHOD#DISABLE_KEYGUARD', 'EVICHECK_START_METHOD#READ_LOGS', 'EVICHECK_ACTIVITY_METHOD#CHANGE_WIFI_MULTICAST_STATE', 'EVICHECK_RECEIVER_METHOD#SET_WALLPAPER_HINTS', 'EVICHECK_PAUSE_METHOD#STATUS_BAR', 'EVICHECK_ONTOUCH_HANDLER#ACCESS_WIFI_STATE', 'EVICHECK_PAUSE_METHOD#CHANGE_COMPONENT_ENABLED_STATE', 'EVICHECK_DESTROY_METHOD#CHANGE_NETWORK_STATE', 'EVICHECK_DESTROY_METHOD#GET_TASKS', 'EVICHECK_SERVICE_METHOD#NFC', 'EVICHECK_RESUME_METHOD#SET_WALLPAPER_HINTS', 'EVICHECK_SERVICE_METHOD#ACCESS_WIFI_STATE', 'EVICHECK_DESTROY_METHOD#RESTART_PACKAGES', 'EVICHECK_START_METHOD#CHANGE_WIFI_MULTICAST_STATE', 'EVICHECK_ONTOUCH_HANDLER#READ_LOGS', 'EVICHECK_RESUME_METHOD#READ_SYNC_STATS', 'EVICHECK_SERVICE_METHOD#SET_TIME', 'EVICHECK_SERVICE_METHOD#READ_SMS', 'EVICHECK_ONCLICK_HANDLER#SEND_SMS', 'EVICHECK_SERVICE_METHOD#READ_HISTORY_BOOKMARKS', 'EVICHECK_ONTOUCH_HANDLER#WRITE_SETTINGS', 'EVICHECK_DESTROY_METHOD#READ_LOGS'])


	policy2=set(['EVICHECK_RECEIVER_METHOD#BLUETOOTH', 'EVICHECK_RECEIVER_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_ACTIVITY_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_DESTROY_METHOD#GET_ACCOUNTS', 'EVICHECK_RECEIVER_METHOD#SEND_SMS', 'EVICHECK_ONTOUCH_HANDLER#ACCESS_COARSE_LOCATION', 'EVICHECK_RECEIVER_METHOD#DISABLE_KEYGUARD', 'EVICHECK_RESTART_METHOD#READ_PHONE_STATE', 'EVICHECK_PAUSE_METHOD#RECORD_AUDIO', 'EVICHECK_SERVICE_METHOD#SEND_SMS', 'EVICHECK_RESUME_METHOD#SET_PREFERRED_APPLICATIONS', 'EVICHECK_ONCREATE_METHOD#READ_LOGS', 'EVICHECK_ONTOUCH_HANDLER#GET_TASKS', 'EVICHECK_ONCLICK_HANDLER#SET_WALLPAPER', 'EVICHECK_SERVICE_METHOD#RECORD_AUDIO', 'EVICHECK_SERVICE_METHOD#ACCESS_COARSE_LOCATION', 'EVICHECK_ONCLICK_HANDLER#KILL_BACKGROUND_PROCESSES', 'EVICHECK_RESTART_METHOD#VIBRATE', 'EVICHECK_SERVICE_METHOD#BLUETOOTH_ADMIN', 'EVICHECK_ACTIVITY_METHOD#SEND_SMS', 'EVICHECK_RECEIVER_METHOD#CAMERA', 'EVICHECK_START_METHOD#AUTHENTICATE_ACCOUNTS', 'EVICHECK_ONCLICK_HANDLER#BROADCAST_STICKY', 'EVICHECK_ONCREATE_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_ACTIVITY_METHOD#EXPAND_STATUS_BAR', 'EVICHECK_SERVICE_METHOD#NFC', 'EVICHECK_RECEIVER_METHOD#READ_SYNC_STATS', 'EVICHECK_RECEIVER_METHOD#WRITE_SETTINGS', 'EVICHECK_ONCREATE_METHOD#SEND_SMS', 'EVICHECK_SERVICE_METHOD#DISABLE_KEYGUARD', 'EVICHECK_PAUSE_METHOD#RESTART_PACKAGES', 'EVICHECK_ONCLICK_HANDLER#WRITE_HISTORY_BOOKMARKS', 'EVICHECK_ONCREATE_METHOD#SET_WALLPAPER', 'EVICHECK_RECEIVER_METHOD#READ_PHONE_STATE', 'EVICHECK_DESTROY_METHOD#READ_LOGS', 'EVICHECK_RECEIVER_METHOD#SET_TIME', 'EVICHECK_DESTROY_METHOD#READ_PHONE_STATE', 'EVICHECK_ONTOUCH_HANDLER#MODIFY_AUDIO_SETTINGS', 'EVICHECK_ONTOUCH_HANDLER#BLUETOOTH', 'EVICHECK_RESUME_METHOD#READ_HISTORY_BOOKMARKS', 'EVICHECK_ONTOUCH_HANDLER#ACCESS_WIFI_STATE', 'EVICHECK_ONCLICK_HANDLER#READ_HISTORY_BOOKMARKS', 'EVICHECK_DESTROY_METHOD#BLUETOOTH', 'EVICHECK_PAUSE_METHOD#CHANGE_COMPONENT_ENABLED_STATE', 'EVICHECK_SERVICE_METHOD#SET_TIME', 'EVICHECK_RESTART_METHOD#READ_LOGS', 'EVICHECK_ONTOUCH_HANDLER#WRITE_SETTINGS', 'EVICHECK_ONTOUCH_HANDLER#READ_LOGS', 'EVICHECK_RESUME_METHOD#READ_SYNC_STATS', 'EVICHECK_SERVICE_METHOD#KILL_BACKGROUND_PROCESSES', 'EVICHECK_DESTROY_METHOD#VIBRATE', 'EVICHECK_SERVICE_METHOD#WRITE_SECURE_SETTINGS', 'EVICHECK_SERVICE_METHOD#READ_HISTORY_BOOKMARKS', 'EVICHECK_DESTROY_METHOD#RESTART_PACKAGES', 'EVICHECK_SERVICE_METHOD#READ_PHONE_STATE', 'EVICHECK_ONCLICK_HANDLER#SEND_SMS'])



	#for pol in policy:
	#	a,b = extract_context_permission(pol)
	#	print a,':','~'+b
	#return
	
	#print policy 
	
	
	
	policy_pairs =   extract_context_permission_as_pairs_for_set(policy)
	print policy_pairs
	
	map_spec = read_spec_file2(f_name)
	counter = 1
	for apk_name, spec in map_spec.iteritems():
		pairs_from_spec =  extract_context_permission_as_pairs_for_set(spec)
		intersect_pairs = policy_pairs.intersection(pairs_from_spec)
		if len(intersect_pairs) > 0:
			print counter
			counter = counter + 1
			
	#return


	dummy, policy_perms =   extract_context_permission_for_set(policy)
	policy_pairs =   extract_context_permission_as_pairs_for_set(policy)
	map_spec = read_spec_file2(f_name)
	counter = 1 
	
	perm_to_freq = {}
	perm_to_freq2 = {}
	pairs_to_freq = {}
	perm_to_context_not_in_policy = {}
	for apk_name, spec in map_spec.iteritems():
		dummy2, perms_from_spec =  extract_context_permission_for_set(spec)
		intersect_only_perms = policy_perms.intersection(perms_from_spec)
		pairs_from_spec =  extract_context_permission_as_pairs_for_set(spec)
		intersect_pairs = policy_pairs.intersection(pairs_from_spec)
		if len(intersect_only_perms) > 0:
			
			print apk_name
			print counter
	 		counter = counter + 1
			if len(intersect_pairs) == 0:
				for perm in intersect_only_perms:
					if perm in perm_to_freq:
						perm_to_freq[perm] = perm_to_freq[perm] + 1
					else:
						perm_to_freq[perm] = 1
				for (c_tmp,p_tmp) in pairs_from_spec:
					if p_tmp in intersect_only_perms:
						if (c_tmp,p_tmp) in pairs_to_freq:
							pairs_to_freq[(c_tmp,p_tmp)] = pairs_to_freq[(c_tmp,p_tmp)] + 1
						else:
							pairs_to_freq[(c_tmp,p_tmp)] = 1

						if (p_tmp) in perm_to_freq2:
							#pairs_to_freq[(c_tmp,p_tmp)] = pairs_to_freq[(c_tmp,p_tmp)] + 1
							perm_to_freq2[(p_tmp)] = perm_to_freq2[(p_tmp)] + 1
						else:
							#pairs_to_freq[(c_tmp,p_tmp)] = 1
							perm_to_freq2[(p_tmp)] = 1
				
	print perm_to_freq2
	print pairs_to_freq
	print perm_to_freq


	set_keys_pairs_cont_perm =  pairs_to_freq.keys()
	map_perm_contex_not_in_policy = {}
	for cont,perm in set_keys_pairs_cont_perm:
		if perm in map_perm_contex_not_in_policy:
			map_perm_contex_not_in_policy[perm].add(cont)
		else:
			map_perm_contex_not_in_policy[perm] = set()
			map_perm_contex_not_in_policy[perm].add(cont)

	for key, val in map_perm_contex_not_in_policy.iteritems():
		print key,val

	
	SimpleName = {}
	SimpleName['EVICHECK_RESUME_METHOD'] = 'RESUME'
	SimpleName['EVICHECK_ONCREATE_METHOD'] = 'CREATE'
	SimpleName['EVICHECK_START_METHOD'] = 'START'
	SimpleName['EVICHECK_PAUSE_METHOD'] = 'PAUSE'
	SimpleName['EVICHECK_STOP_METHOD'] = 'STOP'
	SimpleName['EVICHECK_RESTART_METHOD'] = 'RESTART'
	SimpleName['EVICHECK_DESTROY_METHOD'] = 'DESTROY'
	SimpleName['EVICHECK_ACTIVITY_METHOD'] = 'ACTIVITY'
	SimpleName['EVICHECK_SERVICE_METHOD'] = 'SERVICE'
	SimpleName['EVICHECK_RECEIVER_METHOD'] = 'RECEIVER'
	SimpleName['EVICHECK_ONCLICK_HANDLER'] = 'CLICK'
	SimpleName['EVICHECK_ONTOUCH_HANDLER'] = 'TOUCH'
	
	SimpleName2 = {}
	SimpleName2['EVICHECK_RESUME_METHOD'] = 'RM'
	SimpleName2['EVICHECK_ONCREATE_METHOD'] = 'C'
	SimpleName2['EVICHECK_START_METHOD'] = 'S'
	SimpleName2['EVICHECK_PAUSE_METHOD'] = 'P'
	SimpleName2['EVICHECK_STOP_METHOD'] = 'SP'
	SimpleName2['EVICHECK_RESTART_METHOD'] = 'RS'
	SimpleName2['EVICHECK_DESTROY_METHOD'] = 'D'
	SimpleName2['EVICHECK_ACTIVITY_METHOD'] = 'AM'
	SimpleName2['EVICHECK_SERVICE_METHOD'] = 'SM'
	SimpleName2['EVICHECK_RECEIVER_METHOD'] = 'R'
	SimpleName2['EVICHECK_ONCLICK_HANDLER'] = 'CK'
	SimpleName2['EVICHECK_ONTOUCH_HANDLER'] = 'TC'

	perm_to_context_policy = extract_perm_to_context_for_set(policy)
	
	table = []
	space_line = '& & & \\\\'
	for perm, freq in perm_to_freq.iteritems():
		line = '\parbox{2.5cm}{'+perm+'} ' + ' & ' + str(freq) 

		context_used = ''
		########################################
		if perm in map_perm_contex_not_in_policy:
			for cont in map_perm_contex_not_in_policy[perm]:
				if context_used != '':
					context_used = context_used + ',\\ ' + SimpleName2[cont]
				else:
					context_used = SimpleName2[cont]
		#context_used = ' \parbox{2cm}{ '+ context_used +' } '
		line = line + ' & ' +context_used + ' '	

		########################################
		context_used = ''
		if perm in perm_to_context_policy:
			for cont in perm_to_context_policy[perm]:
				if context_used != '':
					context_used = context_used + ',\\ ' + SimpleName2[cont]
				else:
					context_used = SimpleName2[cont]
		#context_used = ' \parbox{2cm}{ '+ context_used +' } '
		line = line + ' & ' +context_used + ' \\\\'
		########################################
		
		line = line.replace('_','\\_')
		
		table.append(line)
		table.append(space_line)
	print '\n-------------------------------------------------------------\n'
	print table
	for line in table:
		print line
	return



	#dummy, policy1 =   extract_context_permission_for_set(policy)

	#for apk_name, spec in map_spec.iteritems():
	#	dummy2, spec1 =  extract_context_permission_for_set(spec)
	#	intersect_tmp = policy1.intersection(spec1)
	#	if len(intersect_tmp) > 0:
	#		print apk_name
	#		print counter
	#		counter = counter + 1

	#counter2 = 1
	#pol_complement = set(pairs_to_freq.keys())
	#print pol_complement 
	##return
	#for apk_name, spec in map_spec.iteritems():
	#	pair_con_perm =  extract_context_permission_as_pairs_for_set(spec)
	#	intersect_tmp = pol_complement.intersection(pair_con_perm)
	#	if len(intersect_tmp) > 0:
	#		print apk_name
	#		print counter2
	#		counter2 = counter2 + 1
	#counter2 = 1
	#for apk_name, spec in map_spec.iteritems():
	#	dummy2, perms_from_spec =  extract_context_permission_for_set(spec)
	#	if( not policy_perms.issuperset(perms_from_spec)):
	#		print apk_name
	#		print policy_perms
	#		print perms_from_spec
	#		print counter2
	#		counter2 = counter2 + 1
	


def extract_conj_spec_from_spec(spec):
	conj_spec = {}
	for (key,data) in spec.iteritems():
		set_tmp = set()
		data_list = list(data)
		while(len(data_list) > 0):
			current = data_list[0]
			data_list.pop(0)
			for element in data_list:
				conj = current + '&&' + element
				set_tmp.add(conj)
				
		conj_spec[key] = set_tmp
	return conj_spec


def generate_rule_frequency(spec):
	presence_freq = {}
	for key, data in spec.iteritems():
		for element in data:
			if element in presence_freq:
				presence_freq[element] = presence_freq[element] + 1
			else:
				presence_freq[element] = 1
			
			
	return presence_freq




def filter_rules_only_in_first_param(freq1, freq2, k):
	
	kept_rules = {}
	for key, data in freq1.iteritems():
		if key not in freq2:
			kept_rules[key] = data


	
	list_pairs = []
	for key, data in kept_rules.iteritems():
		list_pairs.append((data,key))
		
	sorted_by_freq = sorted(list_pairs, reverse=True)
		
	top_k = []
	count = 0
	for freq, rule in sorted_by_freq:
		if count > k: 
			break
		top_k.append(rule)
		count = count + 1
	return top_k		
		

def add_new_rules_to_specs(spec1, spec_conj_1, spec2, spec_conj_2, rules):
	
	for key, data in spec_conj_1.iteritems():
		for rule in rules:
			if rule in data:
				spec1[key].add(rule)
	
	


	     
	
	

def just_for_test_conjunctive_rules(f_name):
	spec_m = read_spec_file2(f_name+'.mal')
	conj_spec_m = extract_conj_spec_from_spec(spec_m)
	rule_freq_m = generate_rule_frequency(conj_spec_m)

	spec_b = read_spec_file2(f_name+'.ben')
	conj_spec_b = extract_conj_spec_from_spec(spec_b)
	rule_freq_b = generate_rule_frequency(conj_spec_b)
	rules_kept = filter_rules_only_in_first_param(rule_freq_m, rule_freq_b, 10)

	add_new_rules_to_specs(spec_m, conj_spec_m, spec_b, conj_spec_b, rules_kept)
	
	#print spec_m
	
	generate_whole_pb_problem4(spec_m, spec_b, 'permissive')

	
#	print rules_kept
	
	return



	presence_freq = generate_rule_frequency(conj_spec)
	
				
				 
	list_pairs = []
	for key, data in presence_freq.iteritems():
		list_pairs.append((data,key))
	
	print sorted(list_pairs, reverse=True)
			
		#print data2
	#print spec_file
