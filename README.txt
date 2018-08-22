
EviCheck is a tool for Android app certification.  

We assume that the target OS is Linux.

---------------------------------------------------------------------
Installation:
---------------------------------------------------------------------

* Prerequisite: You need to have Python installed, please use version 2.7 to ensure compatibility with Androguard. 
  Also if you want to use the policy generation option, you need to have the Java JRE installed.  

* After extracting the file EviCheck.tat.gz in a chosen directory, for example MY_DIR, you should obtain a directory MY_DIR/EviCheK/ 
  with the following content:  

- README.txt: the current file 
- EviCheck.py: EviCheck program 
- androguard: a directory where androguard should be installed 
- examples/policies: contains example policies
- examples/apps: contains example apps   
- examples/specs/train: contains batch spec files used used for training to generate a policy
- EvichekFiles: contains files used by EviCheck
- solver: the directory where z3 or sat4j should be stored 
- soot: where the InterfaceToSoot binary (runnable JAR) should be stored


* EviCheck is based on androguard by default, so please get androguard from https://code.google.com/p/androguard. 
  
  If you download the version 1.9 for example (https://code.google.com/p/androguard/downloads/detail?name=androguard-1.9.tar.gz) 
  after extracting it you will have the directory androguard-1.9. 
  Copy the content of androguard-1.9/androguard to MY_DIR/EviCheK/androguard.


* If you want to use Soot as back-end, please download InterfaceToSootFlowDroid (http://homepages.inf.ed.ac.uk/mseghir/EviCheck/download.html) and 
  follow the installation instructions. At the end you should obtain the runnable jar file InterfaceToSoot.jar, which needs to be copied 
  to the directory soot.



* NEW: The policy generation option uses the Z3 SMT solver, please get it from https://github.com/Z3Prover/z3 
  Folow the instruction to built it and move the resulting binary named z3 to the directory solver.


* OLD: The policy generation option uses the sat4j solver, please get it from http://www.sat4j.org/. 
  
  We suggest this direct link for the version we have used http://forge.ow2.org/project/download.php?group_id=228&file_id=19135
  After extracting it, place the jar file sat4j-pb.jar in the directory solver. 
  
 


* In case you encounter any installation difficulties, please get in touch, we can provide you with a version of EviCheck containing all the ingredients and ready to use. 



---------------------------------------------------------------------
Usage: 
---------------------------------------------------------------------

We are done! let's now give it a try. 

* Write  python2.7 EviCheck.py --help  to display the available options. We have tested the tool with the version 2.7 of python.  
  

* For a start, use the following command     
      	python2.7  EviCheck.py -f examples/apps/Recorder.apk -g -p examples/policies/recorder.pol -m -t recorder.cert  	

  We are asking EviCheck to check if the app examples/apps/Recorder.apk obeys the policy examples/policies/recorder.pol 
  and it should generate a certificate in the file recorder.cert. The file recorder.pol contains only one rule    

	EVICHECK_ENTRY_POINT ~EVICHECK_ONCLICK_HANDLER : ~RECORD_AUDIO

  It says that permission RECORD_AUDIO should not (~ for negation) be used in any entry point except click handlers.
  As a result we obtain   
       Policy valid!
       which means that the policy is respected by the app.

 We also obtain the file recorder.cert as a certificate. Let us check if the certificate is valid. We write 
       python2.7  EviCheck.py -f examples/apps/Recorder.apk -c -p examples/policies/recorder.pol -m -t recorder.cert  

 We are using the option -c (checking) instead of -g (generation), as this tells EviCheck to check the certificate recorder.cert.
 We obtain the answer 
       Certificate valid!
       Policy valid!

 Meaning that the certificate is valid as well as the policy.         	     	   

 Let us now try to verify another examples/apps/Recorder_bad.apk, we call EviCheck as follows:

       python2.7  EviCheck.py -f examples/apps/Recorder_bad.apk -g -p examples/policies/recorder.pol -m -t recorder.cert

 and we obtain 
       Rule 1  ==>  set(['~EVICHECK_ONCLICK_HANDLER', 'EVICHECK_ENTRY_POINT']) : set(['~RECORD_AUDIO'])
       Policy violated! Tag RECORD_AUDIO is in Lcom/dipak/audiorecording/AudioRecordingActivity->onCreate(Landroid/os/Bundle;)V


 Which means that the policy is violated, in addition to that we get the location where the rule is violated, namely the method 	        
	Lcom/dipak/audiorecording/AudioRecordingActivity->onCreate(Landroid/os/Bundle;)V



Please, get more examples directly form  the Google play store (https://play.google.com/store/apps). The tool http://apps.evozi.com/apk-downloader/ is quite useful to obtain the apk file for each app. We are including other policy files: examples/policies/pol22.pol which is the policy we have automatically 
 generated. We also have the policy examples/policies/pol_gen.pol which contain general rules with multiple permissions. The notation :V means that the 
 concerned rule is an OR-rule, .i.e., the right hand side is a disjunction, by default (:) it's a conjunction. For example
 
 	EVICHECK_ENTRY_POINT EVICHECK_SERVICE_METHOD :V ~READ_PHONE_STATE ~INTERNET

means that in every entry point belonging to a service component, either the READ_PHONE_STATE permission can be used or INTERNET but not both. 
The violation of this might for example indicate that the phone Id is read and sent over the Internet connection using a background service.  



* You can use all the previously illustrated commands having Soot as back-end, for this you just need to add the option -so.	    




---------------------------------------------------------------------
Contact: 
---------------------------------------------------------------------

* For comments, requests and bug reports, please get in touch (mseghir@inf.ed.ac.uk) 



    

 

        
  
  
  
  
 




 


   
