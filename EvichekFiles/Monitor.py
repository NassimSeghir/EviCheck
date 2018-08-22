#######################################################################################################################

# Copyright (C) 2014, Mohamed Nassim Seghir (mseghir@inf.ed.ac.uk) and David Aspinall (David.Aspinall@ed.ac.uk)
# All rights reserved.

#######################################################################################################################


class Monitor:
    init_state = -1 #EVICHECK_INIT_STATE
    def __init__(self, table, actions, final):
        self.transition_table = table
        self.actions_to_consider = actions
        self.final_state = final

    def ComputeSucc(self, state, transition):

        if state == self.final_state:
            return self.final_state

        if transition not in self.actions_to_consider:
            print 'Here: ', transition
            return state

        if((state, transition) in self.transition_table):
            res_tmp = self.transition_table[(state, transition)]
            return res_tmp
        
        else:
            return self.init_state
            
          

    # compute the successor for a block of transitions    
    def ComputeSuccForBlock(self, state, list_transitions):
        if len(list_transitions) == 0 :
            return state
        else:
            res_tmp = state
            for trans in list_transitions:
                res_tmp = self.ComputeSucc( res_tmp, trans) 
                
            return res_tmp
  
 

   # compute the successor for a set of states with respect to a block of transitions    
    def ComputeSetSuccForBlock(self, set_states, list_transitions):

        res = set()
        for state in set_states:
           res_tmp = self.ComputeSuccForBlock(state, list_transitions)
           res.add(res_tmp)
           
        return res
           
 
