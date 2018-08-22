#######################################################################################################################

# Copyright (C) 2014, Mohamed Nassim Seghir (mseghir@inf.ed.ac.uk) and David Aspinall (David.Aspinall@ed.ac.uk)
# All rights reserved.

#######################################################################################################################


class TransitionSystem:
    def __init__(self):
        self.LocToSucc = {}
        self.LocToPreced = {}
        self.TransToLabels = {}
        self.initLoc = None 
        self.finalLoc = "EVICHECK_FINAL_LOC"
        self.LocToSucc[self.finalLoc] = set([])
        self.LocToPreced[self.finalLoc] = set([])

    def AddSucc(self,loc,succ):
        self.LocToSucc[loc] = succ

    def AddPreced(self,loc,pred):
        self.LocToPreced[loc] = pred

    def AddTrans(self, loc1, loc2, labels):
        self.TransToLabels[(loc1,loc2)] = labels

    def Print(self):
        print self.LocToSucc 
        print self.LocToPreced
        print self.TransToLabels


    def SetInitLoc(self,loc):
        self.initLoc = loc
        
