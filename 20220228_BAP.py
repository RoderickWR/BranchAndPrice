# -*- coding: utf-8 -*-
"""
Created on Mon Feb 28 22:32:57 2022

@author: WallrathR
"""


from pyscipopt import *
import numpy as np
import inspect
import matplotlib.pyplot as plt
import re
import random
import time


def entering():
    return print("IN ", inspect.stack()[1][3])  # debugging magic


def leaving():
    return print("OUT ", inspect.stack()[1][3])  # debugging magic


class SameDiff(Conshdlr):
    def consdataCreate(self, name, k, j, constype, node, machineIndex, patternIndex):
        # print("entering consdataCreate")
        cons = self.model.createCons(self, name, stickingatnode=True)
        cons.data = {}
        cons.data["k"] = k
        cons.data["j"] = j
        cons.data["type"] = constype
        cons.data["npropagatedvars"] = 0
        cons.data["npropagations"] = 0
        cons.data["propagated"] = False
        cons.data["node"] = node
        cons.data["machineIndex"] = machineIndex
        cons.data["patternIndex"] = patternIndex # which pattern was the branching var chosen from originally
        return cons

    def checkVariable(self, cons, var, varid, nfixedvars):
        # print("entering checkVariable")
        cutoff = False
        if var.getUbLocal() < 0.5:
            return nfixedvars, cutoff

        constype = cons.data["type"]
        patterns = self.model.data["patterns"]
        patternId = varid
        existitem1 = (patterns[cons.data['machineIndex']][varid][0][cons.data["k"]] < patterns[cons.data['machineIndex']][varid][0][cons.data["j"]])


        if (constype == "required" and (not existitem1)) or (constype == "forbidden" and existitem1):
            # print("fixed variable to zero: ", var)
            infeasible, fixed = self.model.fixVar(var, 0.0)
            if infeasible:
                cutoff = True
            else:
                nfixedvars += 1
        return nfixedvars, cutoff


    def consdataFixVariables(self, cons, result):
        # print("entering consdataFixVariables")
        nfixedvars = 0
        cutoff = False
        v = cons.data["npropagatedvars"]
        while (v < len(opt.lamb[cons.data["machineIndex"]]) and (not cutoff)):
            nfixedvars, cutoff = self.checkVariable(
                cons, opt.lamb[cons.data["machineIndex"]][v], v, nfixedvars)
            v += 1
        if cutoff:
            return {"result": SCIP_RESULT.CUTOFF}
        elif nfixedvars > 0:
            return {"result": SCIP_RESULT.REDUCEDDOM}
        else:
            return result

    def consactive(self, constraint): # Gets called for all constraint that are active in the current node 
        # print("entering consactive")
        # entering()
        if constraint.data["npropagatedvars"] != len(opt.lamb[constraint.data["machineIndex"]]):
            constraint.data["propagated"] = False
            self.model.repropagateNode(constraint.data["node"])
            # print("check node ", constraint.data["node"].getNumber(), "type", constraint.data["type"], "imposed on (k,j) ", (constraint.data["k"],constraint.data["j"]))
        # leaving()

    def consdeactive(self, constraint):
        # print("entering consdeactive")
        # entering()
        constraint.data["npropagatedvars"] = len(opt.lamb[constraint.data["machineIndex"]])
        # leaving()

    def conscheck(
        self,
        constraints,
        solution,
        checkintegrality,
        checklprows,
        printreason,
        completely,
    ):
        # print("entering conscheck")
        for cons in constraints:
            item1 = cons.data["k"]
            item2 = cons.data["j"]
            packings = self.model.data["patterns"][cons.data["machineIndex"]]
            for i in range(len(self.model.data["lamb"][cons.data["machineIndex"]])):
                sol = solution[self.model.data["lamb"][cons.data["machineIndex"]][i]]
                if sol < 0.5:
                    continue
                else:
                    # patternId = i
                    # existitem1 = packings[patternId][item1]
                    # existitem2 = packings[patternId][item2]
                    if cons.data['type'] == 'required' and self.model.data["patterns"][cons.data["machineIndex"]][i][0][item1] > self.model.data["patterns"][cons.data["machineIndex"]][i][0][item2] :
                        # print("conscheck: INFEASIBLE")
                        return {"result": SCIP_RESULT.INFEASIBLE}
                    elif cons.data['type'] == 'forbidden' and self.model.data["patterns"][cons.data["machineIndex"]][i][0][item1] < self.model.data["patterns"][cons.data["machineIndex"]][i][0][item2]:
                        # print("conscheck: INFEASIBLE")
                        return {"result": SCIP_RESULT.INFEASIBLE}
                        

        return {"result": SCIP_RESULT.FEASIBLE}

    def consenfolp(self, constraints, nusefulconss, solinfeasible): # to add cuts
        # print("entering consenfolp")
        pass

    def consenfops(self, constraints, nusefulconss, solinfeasible, objinfeasible):
        # print("entering consenfops")
        pass

    def consprop(self, constraints, nusefulconss, nmarkedconss, proptiming):
        # print("entering consprop")
        result = {"result": SCIP_RESULT.DIDNOTFIND}
        for c in constraints:
            # print("c.data", c.data)
            if not c.data["propagated"]:
                result = self.consdataFixVariables(c, result)
                c.data["npropagations"] += 1
                if result["result"] != SCIP_RESULT.CUTOFF:
                    c.data["propagated"] = True
                    c.data["npropagatedvars"] = len(opt.lamb[c.data["machineIndex"]])
                else:
                    leaving()
                    return {"result": SCIP_RESULT.CUTOFF}
        return result


class MyRyanFosterBranching(Branchrule): # NOT USED
    def __init__(self, model):
        self.model = model

    def branchexeclp(self, allowaddcons):
        lpcands, lpcandssol, lpcandsfrac, nlpcands, npriolpcands, nfracimplvars = self.model.getLPBranchCands()

        fractionalities = np.zeros(
            [len(self.model.data["widths"]), len(self.model.data["widths"])])

        for ii in range(len(lpcands)):

            solval = lpcandssol[ii]

            packingNum = self.model.data["varnames"].index(lpcands[ii].name)

            currentpacking = self.model.data["packings"][packingNum]

            con_id = np.where(np.array(currentpacking) == 1)[0]

            for i in con_id:
                for j in con_id:
                    if i == j:
                        continue
                    fractionalities[i, j] += solval

        temp = np.fmin(fractionalities, 1 - fractionalities)

        x_index, y_index = np.where(temp == np.max(temp))

        row1 = x_index[0]

        row2 = y_index[0]

        childsame = self.model.createChild(
            0.0, self.model.getLocalTransEstimate())

        childdiff = self.model.createChild(
            0.0, self.model.getLocalTransEstimate())

        conssame = self.model.data["conshdlr"].consdataCreate(
            "some_same_name", row1, row2, "same", childsame)

        consdiff = self.model.data["conshdlr"].consdataCreate(
            "some_diff_name", row1, row2, "diff", childdiff)

        self.model.addConsNode(childsame, conssame)

        self.model.addConsNode(childdiff, consdiff)

        self.model.data['branchingCons'].append(conssame)

        self.model.data['branchingCons'].append(consdiff)

        return {"result": SCIP_RESULT.BRANCHED}


class MyVarBranching(Branchrule):
    def __init__(self, model):
        self.model = model
        
        
    def checkAlreadyBranched(self,k,j, machineIndex):
        alreadyBranched = False
        
        iterNode = self.model.getCurrentNode()
        iterDepth = self.model.getCurrentNode().getDepth()
        
        for i in range(iterDepth): # go upstream path in the tree
            
        
            if iterNode.getAddedConss() != []: # check if current node has a constraint attached
                branchedOrgVar = [int(x) for x in iterNode.getAddedConss()[0].name if x.isdigit()] # get the original variable that is branched on in the current node
                if (branchedOrgVar[0] == k and branchedOrgVar[1] == j and branchedOrgVar[2] == machineIndex) or (branchedOrgVar[0] == j and branchedOrgVar[1] == k and branchedOrgVar[2] == machineIndex) : # was the variable k,j already branched on in this node?
                    return True
                else:
                    alreadyBranched = False
            
            iterNode = iterNode.getParent()
        
        return alreadyBranched
    
    
    def checkAlreadyBranchedImpl(self,k,j, machineIndex):
        alreadyBranchedImpl = False
        
        iterNode = self.model.getCurrentNode()
        iterDepth = self.model.getCurrentNode().getDepth()
        
        if iterDepth == 0: # if at root node, cannot have alreadyBranchedImpl = True
            return alreadyBranchedImpl
        
        branchedOrgVarList = []
        
        for i in range(iterDepth): # go upstream path in the tree
            if iterNode.getAddedConss() != []:
                consnameshort = [[int(x) for x in iterNode.getAddedConss()[0].name if x.isdigit()], 1 if (iterNode.getAddedConss()[0].name[0] == 'r') else 0]
                if iterNode.getAddedConss() != [] and consnameshort[0][2] == machineIndex: # check if current node has a constraint attached
                    branchedOrgVarList.append(consnameshort) # get the original variable that is branched on in the current node
            iterNode = iterNode.getParent()
        
        for i in range(len(branchedOrgVarList)): # make the list contain required constraints only
            if branchedOrgVarList[i][1] == 0: 
                temp00 = branchedOrgVarList[i][0][0] #switch order...
                branchedOrgVarList[i][0][0] = branchedOrgVarList[i][0][1]
                branchedOrgVarList[i][0][1] = temp00
                branchedOrgVarList[i][1] = 1 # ...and change cons type
        
        k_iter = -1
        for c in branchedOrgVarList: # example: branchedOrgVarList = [([1, 2], 1), ([2, 0], 1)]
            if c[0][0] == k: # when c = ([2, 0], 1) true if k = 2
                k_iter = c[0][1] # set k_iter to the pointer to the next element
                found = False
                while found == False:
                    k_iter, found = self.checkFurther(k_iter, j, branchedOrgVarList, "forward")
                        
            elif c[0][1] == k: 
                k_iter = c[0][0] # set k_iter to the pointer to the next element
                found = False
                while found == False:
                    k_iter, found = self.checkFurther(k_iter, j, branchedOrgVarList, "backwards")
            
        if k_iter != -1:
            alreadyBranchedImpl = True
                
                
        return alreadyBranchedImpl
      
    def checkFurther(self, k_iter, j, branchedOrgVarList, sense):
        ret_found = False
        ret_k_iter = k_iter
        
        if sense == "forward":
            for c in branchedOrgVarList:
                if c[0][0] == k_iter and c[0][1] == j: # relation between k and j found, end search
                    return c[0][1], True
                elif c[0][0] == k_iter and c[0][1] != j: # no relation between k and j found yet, continue search
                    ret_found = False
                    ret_k_iter = c[0][1]
                else:
                    return -1, True # if neither a next element exists nor this element points to j => no relation between k and j, end search
            return ret_k_iter, ret_found
        else:
            for c in branchedOrgVarList:
                if c[0][1] == k_iter and c[0][0] == j: # relation between k and j found, end search
                    return c[0][0], True
                elif c[0][1] == k_iter and c[0][0] != j: # no relation between k and j found yet, continue search
                    ret_found = False
                    ret_k_iter = c[0][0]
                else:
                    return -1, True # if neither a next element exists nor this element points to j => no relation between k and j, end search
            return ret_k_iter, ret_found

            
    def determineBranchingVar(self, machineIndex): # org variable to branch on for a balanced tree in terms of patterns, takes into account fixed-status of patterns and already branched  
        # print("entering determineBranchingVar")
        ratio_branches = 0
        k_found,j_found = -1,-1
        for k in range(opt.numberJobs): # for each element in order matrix
            for j in range(opt.numberJobs):
                if k != j:
                    
                    # alreadyBranched = self.checkAlreadyBranched(k,j, machineIndex) # check whether (k,j) was already branched on in all of the constraints of this node 
                    
                    # alreadyBranchedImpl = self.checkAlreadyBranchedImpl(k,j, machineIndex) # check whether (k,j) was already branched on in all of the constraints of this node 
                
                    
                    ratio_branches_new = 0
                    
                    # if alreadyBranchedImpl:
                        # print("here")
                    
                    # if (not alreadyBranched and not alreadyBranchedImpl): # NOT NEEDED, INSTEAD ASSERT IN THE END
                    # if (not alreadyBranched): # NOT NEEDED, INSTEAD ASSERT IN THE END

                    
                    sumrequired = np.sum([opt.lamb[machineIndex][i].getLPSol() for i in range(len(self.model.data["patterns"][machineIndex])) if self.model.data["patterns"][machineIndex][i][0][k] < self.model.data["patterns"][machineIndex][i][0][j] ] ) #add together lambda values of patterns on machine [Index] that have job k before j and that were not fix to 0 yet
                    sumforbidden = np.sum([opt.lamb[machineIndex][i].getLPSol() for i in range(len(self.model.data["patterns"][machineIndex])) if self.model.data["patterns"][machineIndex][i][0][k] > self.model.data["patterns"][machineIndex][i][0][j] ] ) #add together lambda values of patterns on machine [Index] that do not have job k before j and that were not fix to 0 yet
                    # print("currentNode number: ", self.model.getCurrentNode().getNumber())
                    # print("sumrequired ", sumrequired)
                    # print("sumforbidden ", sumforbidden)
                    
                    ratio_branches_new = np.fmin(sumrequired, sumforbidden)/np.fmax(sumrequired, sumforbidden) # smaller branch divided by bigger branch, should be near 1 for balanced tree
                    # print("ratio_branches_new" , ratio_branches_new)
                    if ratio_branches < ratio_branches_new:
                            ratio_branches = ratio_branches_new
                            # print("ratio_branches" , ratio_branches)
                            k_found,j_found = k,j
                        
        
        # print("found branching candidate (k,j) ", (k_found,j_found))
        return k_found,j_found 

    def branchexeclp(self, allowaddcons):

        (
            lpcands,
            lpcandssol,
            lpcandsfrac,
            nlpcands,
            npriolpcands,
            nfracimplvars,
        ) = self.model.getLPBranchCands()
        opt.branchexeclpCounter += 1
        t = time.time()
        # print("entering branchexeclp")
        # print("lpcandssol: ", lpcandssol)
    
        integral = lpcands[0] #take the first candidate # IS THIS NECESSARY?
        
        patternInd = [int(s) for s in re.findall(r'\b\d+\b', integral.name)] #which pattern is meant by the lambda variable
        
        pattern = patterns[patternInd[0]][patternInd[1]] #retrieve the corresponding pattern, ind[0] is the machine, ind[1] the pattern
        
        pricing = list(self.model.data["pricer"].pricingList.items())[patternInd[0]][1] #get the corresponding pricing problem NOT USED
        
        k_found,j_found = self.determineBranchingVar(patternInd[0]) # find the order variable to branch on, on the first lambda candidates machine
        
        if k_found == -1 and j_found == -1:
            # print("lpcands, lpcandssol:", lpcands, lpcandssol)
            return {"result": SCIP_RESULT.CUTOFF}
    
        childsmaller = self.model.createChild(
            0.0, self.model.getLocalEstimate())

        childbigger = self.model.createChild(
            0.0, self.model.getLocalEstimate())
        
        # print("Created required child with (ParentID,ID) ", (childsmaller.getParent().getNumber(), childsmaller.getNumber()) )
        # print("Created forbidden child with (ParentID,ID) ", (childbigger.getParent().getNumber(), childbigger.getNumber()) )
        conssmaller = self.model.data["conshdlr"].consdataCreate(
            "required_(%s%s)_m(%s)"%(k_found,j_found,patternInd[0]), k_found,j_found, "required", childsmaller, patternInd[0], patternInd[1])


        consbigger = self.model.data["conshdlr"].consdataCreate(
            "forbidden_(%s%s)_m(%s)"%(k_found,j_found,patternInd[0]), k_found,j_found, "forbidden", childbigger, patternInd[0], patternInd[1])
        
        self.model.addConsNode(childsmaller, conssmaller)

        self.model.addConsNode(childbigger, consbigger)

        self.model.data['branchingCons'].append(conssmaller)

        self.model.data['branchingCons'].append(consbigger)

        opt.branchexeclpTimer += time.time() - t
        return {"result": SCIP_RESULT.BRANCHED}

# Pricing creates one pricing problem. You need to provide the processing times matrix, the machine index, and the dual information to form the objective
class Pricing:

    def __init__(self, initProcessingTimes, i, n, beta, gamma):
        self.n = n
        self.s = {}
        self.f = {}
        self.x = {}
        self.processing_times = initProcessingTimes
        self.machineIndex = i
        self.bigM = 100
        self.pricing = Model()
        self.beta = beta
        self.gamma = gamma
        # self.omega = omega
        self.createPricing()

    def createPricing(self):

        # 2) CREATE PRICING

        self.pricing.hideOutput()
        # self.pricing.params.outputflag = 0
        # self.pricing.modelSense = GRB.MINIMIZE

        for j in range(0, self.n):
            self.s[j] = self.pricing.addVar(
                vtype="C", name="start(%s)" % (j), lb=0.0, ub=100.0, obj = -1.0 * self.beta[j])
            self.f[j] = self.pricing.addVar(
                vtype="C", name="finish(%s)" % (j), lb=0.0, ub=100.0, obj = -1.0 * self.gamma[j])

        # Create order matrix
        for k in range(0, self.n):
            for j in range(0, self.n):
                self.x[k, j] = self.pricing.addVar(
                    vtype="B", name="x(%s,%s)" % (k, j))        
                


        for j in range(0, self.n):
            self.pricing.addCons(self.s[j] + self.processing_times[j,
                                  self.machineIndex] == self.f[j], "startFinish(%s)" % (j))

        for j in range(0, self.n):
            for k in range(0, self.n):
                if k != j:
                    self.pricing.addCons(
                        self.x[j, k] + self.x[k, j] == 1, "precedence(%s)" % (j))
                # if j => k, then start time of j should be 0
                self.pricing.addCons(self.s[j] <= (
                    (self.n - 1)-quicksum(self.x[j, k] for k in range(self.n) if k != j))*50, "fixAtZero(%s)" % (j))

        for k in range(0, self.n):
            for j in range(0, self.n):
                # for each job k the finishing date one machine i has to be smaller than the starting date of the next job j, (1) if j follows k on i, (2) if job k was not the cutoff job (last job) on i
                self.pricing.addCons(
                    self.f[k] <= self.s[j] + self.bigM*(1-self.x[k, j]), "finishStart(%s)" % (k))
                
class PricingLastMachine:

    def __init__(self, initProcessingTimes, i, n, beta, gamma,d_makespan):
        self.n = n
        self.s = {}
        self.f = {}
        self.x = {}
        self.processing_times = initProcessingTimes
        self.machineIndex = i
        self.bigM = 100
        self.pricing = Model()
        self.beta = beta
        self.gamma = gamma
        # self.omega = omega
        self.d_makespan = d_makespan
        self.createPricing()

    def createPricing(self):

        # 2) CREATE PRICING

        self.pricing.hideOutput()
        # self.pricing.params.outputflag = 0
        # self.pricing.modelSense = GRB.MINIMIZE
        self.makespan = self.pricing.addVar(
                vtype="C", name="makespan", lb=0.0, ub=100.0, obj = -1.0 *self.d_makespan) #objective coefficient in org. problem is 1
        for j in range(0, self.n):
            self.s[j] = self.pricing.addVar(
                vtype="C", name="start(%s)" % (j), lb=0.0, ub=100.0, obj = -1.0 * self.beta[j])
            self.f[j] = self.pricing.addVar(
                vtype="C", name="finish(%s)" % (j), lb=0.0, ub=100.0, obj = -1.0 * self.gamma[j])

        # Create order matrix
        for k in range(0, self.n):
            for j in range(0, self.n):
                self.x[k, j] = self.pricing.addVar(
                    vtype="B", name="x(%s,%s)" % (k, j))        
                


        for j in range(0, self.n):
            self.pricing.addCons(self.s[j] + self.processing_times[j,
                                  self.machineIndex] == self.f[j], "startFinish(%s)" % (j))

        for j in range(0, self.n):
            for k in range(0, self.n):
                if k != j:
                    self.pricing.addCons(
                        self.x[j, k] + self.x[k, j] == 1, "precedence(%s)" % (j))
                # if j => k, then start time of j should be 0
                self.pricing.addCons(self.s[j] <= (
                    (self.n - 1)-quicksum(self.x[j, k] for k in range(self.n) if k != j))*50, "fixAtZero(%s)" % (j))

        for k in range(0, self.n):
            for j in range(0, self.n):
                # for each job k the finishing date one machine i has to be smaller than the starting date of the next job j, (1) if j follows k on i, (2) if job k was not the cutoff job (last job) on i
                self.pricing.addCons(
                    self.f[k] <= self.s[j] + self.bigM*(1-self.x[k, j]), "finishStart(%s)" % (k))        
                
        for j in range(0, self.n):
            self.pricing.addCons(self.makespan >=  self.f[j], "makespanConstrMachine(%s)" % (j))
        
# Pricer is the pricer plugin from pyscipopt. In the reduced costs function new patterns will be generated during BAP
class Pricer(Pricer):
    def addBranchingDecisionConss(self, modelIN, machineIndex):
        # print("entering addBranchingDecisionsConss")
        for cons in self.model.data['branchingCons']:
            if (not cons.isActive()):
                continue
            elif cons.data["machineIndex"] != machineIndex:
                continue
            item1 = cons.data['k']
            item2 = cons.data['j']

            if cons.data['type'] == 'required':
                # print("Enforce required (k,j) ", (item1, item2), "on node ", cons.data['node'].getNumber())
                modelIN.pricing.addCons(modelIN.x[item1,item2] == 1, "requireOrder(%s%s)_onNode_(%s)"%(item1,item2,cons.data['node'].getNumber()))

            elif cons.data['type'] == 'forbidden':
                # print("Enforce forbidden (k,j) ", (item1, item2), "on node ", cons.data['node'].getNumber())
                modelIN.pricing.addCons(modelIN.x[item1,item2] == 0, "forbiddenOrder(%s%s)_onNode_(%s)"%(item1,item2,cons.data['node'].getNumber()))

    def addFixedVarsConss(self, modelIN, machineIndex):
        
        ind = 0
        # for i in self.model.data["lamb"][machineIndex]:
        #     # print("getUBLocal", i.getUbLocal())
        #     if i.getUbLocal() < 0.5:
        #         modelIN.pricing.addCons(quicksum(quicksum(modelIN.x[k,j] for j in range(4) if k != j and self.model.data["patterns"][machineIndex][ind][k][j] == 1) for k in range(4))  <= np.sum(self.model.data["patterns"][machineIndex][ind]) - self.model.data["patterns"][machineIndex][ind][0][0] - self.model.data["patterns"][machineIndex][ind][1][1] - self.model.data["patterns"][machineIndex][ind][2][2] - self.model.data["patterns"][machineIndex][ind][3][3] - 1, "NoPat(%s)_m%s"%(i,machineIndex))
        #     ind += 1

    # The reduced cost function for the variable pricer
    def pricerredcost(self):
        opt.pricerredcostCounter  += 1
        t = time.time()
        # print("entering pricerredcost")
        # Retrieving the dual solutions
        dualSolutionsAlpha = []
        dualSolutionsBeta = []
        dualSolutionsGamma = []
        # dualSolutionsOmega = {}
        dualSolutionsMakespan = 0
        
        for i, c in enumerate(self.data["alphaCons"]):
            dualSolutionsAlpha.append(self.model.getDualsolLinear(c))
            # dualSolutions.append(self.model.getDualsolSetppc(c))
        for i, c in enumerate(self.data["betaCons"]):
            dualSolutionsBeta.append(self.model.getDualsolLinear(c))
        for i, c in enumerate(self.data["gammaCons"]):
            dualSolutionsGamma.append(self.model.getDualsolLinear(c))
        # for i in range(self.data["m"]):
        #     dualSolutionsOmega[i] = {}
        #     for (key,value) in self.data["omegaCons"][i].items():
        #         dualSolutionsOmega[i][key] = self.model.getDualsolLinear(value)
        dualSolutionsMakespan = self.model.getDualsolLinear(self.data["makespanCons"])         

              
        # create pricing list using the current dual information from the master
        self.pricingList = self.createPricingList(dualSolutionsBeta, dualSolutionsGamma,dualSolutionsMakespan)  # a list of m pricing problems
        
        # counts pricing problems that cannot find negative reduced costs
        nbrPricingOpt = 0

        # iterate through the pricing list
        for i, (key, pricing) in enumerate(self.pricingList.items()):
            
            
            # Avoid to generate columns which are fixed to zero
            self.addFixedVarsConss(pricing, i)
            
            # Add branching decisions constraints to the sub SCIP
            self.addBranchingDecisionConss(pricing, i)
            
            # pricing.pricing.redirectOutput()
            pricing.pricing.optimize()
            
            # print("pricing solution status: ", pricing.pricing.getStatus())
            # if pricing.pricing.getStatus() == 'infeasible':
            #     print("infeas")
            random.seed(10)
            # pertub = random.gauss(0,0.1)
            # pertub = random.uniform(0,15)
            pertub = 0
            
            #check negative reduced costs
            if pricing.pricing.getObjVal() + pertub - dualSolutionsAlpha[i] < -1e-5:
                
              # print("Red costs on machine ", i, "is ", pricing.pricing.getObjVal() + pertub - dualSolutionsAlpha[i]  )  
              sols = pricing.pricing.getSols()
              # print("number of solutions: ", len(sols))
              # for j in range(int(np.rint(len(sols)/(opt.inputParam+1)+1)) if len(sols) > 2 else len(sols)):
              for j in range(opt.inputParam*2 if len(sols) > opt.inputParam*2 else len(sols)):
              
                  # retrieve pattern 
                  newPattern = self.retrieveXMatrixMulti(sols[j], pricing)
                  
                  # add new pattern to master
                  self.addNewPattern(newPattern, i)
              
              # opt.master.data["patterns"][i].append(newPattern)
              # # print("Add pattern ", newPattern, " is added for machine " , i )

              # # create new lambda variable for that pattern
              # newVar = opt.master.addVar(vtype="B", pricedVar=True, name = "lamb_m(%s)p(%s)"%(i,len(opt.master.data["patterns"][i]) - 1))
              
              # # add the lambda variable to the master
              # opt.master.data["lamb"][i].append(newVar)
              
              
              # # add the new variable to the master constraints for machine i
              # opt.master.addConsCoeff(opt.master.data["alphaCons"][i], newVar, 1)
              
              # for ind, c in enumerate(self.data["betaCons"][i*opt.numberJobs:(i+1)*opt.numberJobs]):
              #     opt.master.addConsCoeff(c, newVar, newPattern[0][ind - i*opt.numberJobs])
               
              # for ind, c in enumerate(self.data["gammaCons"][i*opt.numberJobs:(i+1)*opt.numberJobs]):
              #     opt.master.addConsCoeff(c, newVar, newPattern[1][ind - i*opt.numberJobs])
              
              # for (key,value) in opt.master.data["omegaCons"][i].items():
              #     # print("key", key)
              #     # print("value", value)
              #     # print("newPattern[int(key[0])][int(key[1])]",newPattern[int(key[0])][int(key[1])])
              #     opt.master.addConsCoeff(value, newVar, newPattern[int(key[0])][int(key[1])]*opt.bigM)
   
            # increment counter if machine i does not find any new patterns with negative reduced costs      
            if pricing.pricing.getObjVal() - dualSolutionsAlpha[i] >= -1e-5:
              nbrPricingOpt += 1
       
        # print("pricing done")    
        opt.pricerredcostTimer += time.time() - t
        return {"result": SCIP_RESULT.SUCCESS}
    
    def addNewPattern(self, newPattern, i):
        opt.master.data["patterns"][i].append(newPattern)
        # print("Add pattern ", newPattern, " is added for machine " , i )

        # create new lambda variable for that pattern
        newVar = opt.master.addVar(vtype="B", pricedVar=True, name = "lamb_m(%s)p(%s)"%(i,len(opt.master.data["patterns"][i]) - 1))
        
        # add the lambda variable to the master
        opt.master.data["lamb"][i].append(newVar)
        
        
        # add the new variable to the master constraints for machine i
        opt.master.addConsCoeff(opt.master.data["alphaCons"][i], newVar, 1)
        
        for ind, c in enumerate(self.data["betaCons"][i*opt.numberJobs:(i+1)*opt.numberJobs]):
            opt.master.addConsCoeff(c, newVar, newPattern[0][ind ])
         
        for ind, c in enumerate(self.data["gammaCons"][i*opt.numberJobs:(i+1)*opt.numberJobs]):
            opt.master.addConsCoeff(c, newVar, newPattern[1][ind ])
        if i == opt.numberMachines-1:
            opt.master.addConsCoeff(self.data["makespanCons"],newVar, newPattern[2])
    
    # retrieve a pattern from modelIN
    def retrieveXMatrix(self,pricerIN):
        matrix = np.zeros((self.data["n"],self.data["n"]))
        mat = []
        mat = [[pricerIN.pricing.getVal(pricerIN.s[j]) for j in range(0,self.data["n"])],[pricerIN.pricing.getVal(pricerIN.f[j]) for j in range(0,self.data["n"])]]
        
        return mat  
    
    # retrieve a pattern from modelIN
    def retrieveXMatrixMulti(self, solIN, pricerIN):
        matrix = np.zeros((self.data["n"],self.data["n"]))
        mat = []
        mat = [[pricerIN.pricing.getSolVal(solIN, pricerIN.s[j]) for j in range(0,self.data["n"])],[pricerIN.pricing.getSolVal(solIN, pricerIN.f[j]) for j in range(0,self.data["n"])],max(pricerIN.pricing.getSolVal(solIN, pricerIN.f[j]) for j in range(0,self.data["n"]))]
        
        return mat 
    
    def createPricingList(self, dualSolutionsBeta, dualSolutionsGamma,dualSolutionsMakespan):
        # PARAMS
        # job 1 takes 7 hours on machine 1, and 1 hour on machine 2, job 2 takes 1 hour on machine 1, and 7 hours on machine 2
        pricingList = {}
        for i in range(0, opt.numberMachines):
            if i < opt.numberMachines-1:
                pricing = Pricing(opt.processing_times, i, opt.numberJobs, dualSolutionsBeta[(i*opt.numberJobs):((i+1)*opt.numberJobs)], dualSolutionsGamma[(i*opt.numberJobs):((i+1)*opt.numberJobs)])
            else:
                pricing = PricingLastMachine(opt.processing_times, i, opt.numberJobs, dualSolutionsBeta[(i*opt.numberJobs):((i+1)*opt.numberJobs)], dualSolutionsGamma[(i*opt.numberJobs):((i+1)*opt.numberJobs)], dualSolutionsMakespan)    
            pricingList["pricing(%s)" % i] = pricing
    
        return pricingList
    
    # The initialisation function for the variable pricer to retrieve the transformed constraints of the problem
    def pricerinit(self):
        for i, c in enumerate(self.data["alphaCons"]):
            self.data["alphaCons"][i] = self.model.getTransformedCons(c)
        for i, c in enumerate(self.data["betaCons"]):
            self.data["betaCons"][i] = self.model.getTransformedCons(c)
        for i, c in enumerate(self.data["gammaCons"]):
            self.data["gammaCons"][i] = self.model.getTransformedCons(c)
        # for i in range(self.data["m"]):
        #     for (key,value) in self.data["omegaCons"][i].items():
        #         self.data["omegaCons"][i][key] = self.model.getTransformedCons(value)
        self.data["makespanCons"] = self.model.getTransformedCons(self.data["makespanCons"])

    


# In Optimizer, (1) the master problem and the flow shop parameters are defined, (2) the BAP algorithm is configured and executed, (3) the Gantt is drawn
class Optimizer: 
    
    def __init__(self,initPatterns,initProcessingTimes,n,m, inputParam): 
        self.numberJobs = n
        self.numberMachines = m
        self.s = []
        self.f = []
        self.x = []
        self.alphaCons = []
        self.betaCons = []
        self.gammaCons = []
        self.omegaCons = {}
        self.lamb = [ [] for _ in range(self.numberMachines) ]
        self.offset = []
        self.processing_times = initProcessingTimes
        self.patterns = initPatterns
        self.master = Model()
        self.bigM = 100
        self.nodeID = 1
        self.pricerredcostCounter = 0
        self.pricerredcostTimer = 0
        self.branchexeclpCounter = 0
        self.branchexeclpTimer = 0
        self.inputParam = inputParam # for experiments
                


    def test(self):

    
        # master.setPresolve(SCIP_PARAMSETTING.OFF)
    

        self.master.setIntParam("presolving/maxrestarts", 0)
    
        self.master.setParam('limits/time', 30 * 60)
    
        self.master.setSeparating(SCIP_PARAMSETTING.OFF)
    
        # self.master.setHeuristics(SCIP_PARAMSETTING.OFF)
    
        self.master.setObjIntegral()
    
        pricer = Pricer(priority=5000000)
        self.master.includePricer(pricer, "BinPackingPricer", "Pricer")
    
        conshdlr = SameDiff()
    
        self.master.includeConshdlr(
            conshdlr,
            "SameDiff",
            "SameDiff Constraint Handler",
            chckpriority=2000000,
            propfreq=1,
        )
    
        # my_branchrule = MyRyanFosterBranching(self.master)

    
        my_branchrule = MyVarBranching(self.master)
    
        self.master.includeBranchrule(
            my_branchrule,
            "test branch",
            "test branching and probing and lp functions",
            priority=10000000,
            maxdepth=-1,
            maxbounddist=1,
        )
          
    
    
        #### Master problem 
        
        # Create lambda variables for these patterns.
        for i in range(0, self.numberMachines):
            for l in range(len(self.patterns[i])):
                self.lamb[i].append(self.master.addVar(vtype="C", name = "lamb_m(%s)p(%s)"%(i,l) ))  # is pattern p used on machine i
            self.offset.append(self.master.addVar(vtype="C", name = "offset_m%s"%i )) 
    
            for j in range(0, self.numberJobs):
                self.s.append(self.master.addVar(vtype="C", name = "start_m(%s)j(%s)"%(i,j)))
                self.f.append(self.master.addVar(vtype="C", name = "finish_m(%s)j(%s)"%(i,j)))
    
            self.alphaCons.append(self.master.addCons(quicksum( self.lamb[i][l] for l in range(len(self.patterns[i]))) - 1 == 0, "convexityOnMachine(%s)" % (i), separate=False, modifiable=True))  # only one pattern per machine
    
        # define makespan
        c_max = self.master.addVar(vtype="C", name="makespan", obj=1.0)
    
        for i in range(0, self.numberMachines):
        #     self.omegaCons[i] = {}
        #     for k in range(0,self.numberJobs):
        #         for j in range(0,self.numberJobs):
        #             if k != j:
        #                 self.omegaCons[i]["%s%s"%(k,j)] = self.master.addCons(self.f[k + i*self.numberJobs] - self.s[j + i*self.numberJobs] - self.bigM*(1-quicksum(self.patterns[i][l][k][j]*self.lamb[i][l] for l in range(len(self.patterns[i]))) ) <=  0, "finishStart(%s,%s,%s)"%(i,k,j), separate=False, modifiable=True) # for each job k the finishing date one machine i has to be smaller than the starting date of the next job j, (1) if j follows k on i, (2) if job k was not the cutoff job (last job) on i 
            for j in range(0, self.numberJobs):
                self.betaCons.append(self.master.addCons(quicksum( self.patterns[i][l][0][j]* self.lamb[i][l] for l in range(len( self.patterns[i]))) +
                                                                    self.offset[i] -  self.s[j + i* self.numberJobs] == 0, separate=False, modifiable=True, name = "startCon_m(%s)j(%s)" %(i,j))) # starting time on machine i for job j is determined by the starting time of job j in the selected pattern p
                # completion time on machine i for job j is determined by the completion time of job j in the selected pattern p
                self.gammaCons.append(self.master.addCons(quicksum( self.patterns[i][l][1][j]* self.lamb[i][l] for l in range(len( self.patterns[i]))) +  self.offset[i] -  self.f[j + i* self.numberJobs] == 0, separate=False, modifiable=True, name = "finishCon_m(%s)j(%s)" %(i,j)))
            if i !=  self.numberMachines-1:
                for j in range(0, self.numberJobs):
                    self.master.addCons( self.f[j + i*self.numberJobs] <=  self.s[j + (i+1)*self.numberJobs],
                                   "interMachine(%s,%s)" % (i, j))
            for j in range(0, self.numberJobs):
                self.master.addCons( self.s[j + i*self.numberJobs] +  self.processing_times[j, i] ==  self.f[j + i* self.numberJobs],
                               "startFinish(%s,%s)" % (i, j))
    
        # for j in range(0, self.numberJobs):
        #     self.master.addCons(c_max >=  self.f[j + ( self.numberMachines-1)* self.numberJobs], "makespanConstrMachine(%s)" % (j))
        self.makespanCons = self.master.addCons(quicksum( self.patterns[self.numberMachines-1][l][2]* self.lamb[self.numberMachines-1][l] for l in range(len( self.patterns[self.numberMachines-1]))) + self.offset[self.numberMachines-1] - c_max == 0 , separate=False, modifiable=True, name= "makespanCons")    
        #### End         
    
            
        pricer.data = {}
        pricer.data["alphaCons"] =  self.alphaCons
        pricer.data["betaCons"] =  self.betaCons
        pricer.data["gammaCons"] =  self.gammaCons
        pricer.data["makespanCons"] =  self.makespanCons
        # pricer.data["omegaCons"] =  self.omegaCons
        pricer.data["m"] =  self.numberMachines
        pricer.data["n"] =  self.numberJobs
    
        self.master.data = {}
        self.master.data["s"] =  self.s
        self.master.data["f"] =  self.f
        self.master.data["offset"] =  self.offset
        self.master.data["lamb"] =  self.lamb
        self.master.data["alphaCons"] =  self.alphaCons
        self.master.data["betaCons"] =  self.betaCons
        self.master.data["gammaCons"] =  self.gammaCons
        self.master.data["makespanCons"] =  self.makespanCons
        # self.master.data["omegaCons"] =  self.omegaCons
        self.master.data["patterns"] =  self.patterns
        self.master.data["conshdlr"] = conshdlr
        self.master.data["pricer"] = pricer
        self.master.data['branchingCons'] = []
        
        self.master.redirectOutput()
        self.master.optimize()
        
    # Draw a Gantt chart 
    
        # x_array = restructureX(x,m,n) #input x dictionary from solved model, output x numpy array
        fig = plt.figure()
        M = ['red', 'blue', 'yellow', 'orange', 'green', 'moccasin', 'purple', 'pink', 'navajowhite', 'Thistle',
             'Magenta', 'SlateBlue', 'RoyalBlue', 'Aqua', 'floralwhite', 'ghostwhite', 'goldenrod', 'mediumslateblue',
             'navajowhite', 'navy', 'sandybrown']
        M_num = 0
        for i in range(self.numberMachines):
            for j in range(self.numberJobs):
    
                Start_time = self.master.getVal(self.master.data["s"][j + i*self.numberJobs])
                End_time = self.master.getVal(self.master.data["f"][j + i*self.numberJobs])
    
                # Job=np.nonzero(x_array[j,:,i] == 1 )[0][0] # for each machine and each job position, find the job that takes this position
                Job = j
                plt.barh(i, width=End_time - Start_time, height=0.8, left=Start_time,
                         color=M[Job], edgecolor='black')
                plt.text(x=Start_time + ((End_time - Start_time) / 2 - 0.25), y=i - 0.2,
                         s=Job+1, size=15, fontproperties='Times New Roman')
                M_num += 1
        plt.yticks(np.arange(M_num + 1), np.arange(1, M_num + 2),
                   size=8, fontproperties='Times New Roman')
        plt.xticks(np.arange(0, self.master.getObjVal() + 1, 1.0),
                   size=8, fontproperties='Times New Roman')
        plt.ylabel("machine", size=20, fontproperties='SimSun')
        plt.xlabel("time", size=20, fontproperties='SimSun')
        plt.tick_params(labelsize=20)
        plt.tick_params(direction='in')
        plt.show()
        
        solutiondict = {}
        #post solve prints        
        for i in range(opt.numberMachines):
            print("Number of Patterns machine (%s)"%i, "is ", len(opt.lamb[i]))
            solutiondict["numPat_m_%s"%i] = len(opt.lamb[i])
            
        print("Pricerredcost invoked ", opt.pricerredcostCounter, " times")
        solutiondict["numInvPricer"] = opt.pricerredcostCounter
        print("Pricerredcost took ", opt.pricerredcostTimer, " seconds")
        solutiondict["timePricer"] = opt.pricerredcostTimer
        print("Branchexeclp invoked ", opt.branchexeclpCounter, " times")
        solutiondict["numInvBranching"] = opt.branchexeclpCounter
        print("Branchexeclp took ", opt.branchexeclpTimer, " seconds")
        solutiondict["timeBranching"] = opt.branchexeclpTimer

        return solutiondict

if __name__ == "__main__":
    
        # PARAMS
        n = 5  # number of jobs
        m = 3  # number of machines
        # job 1 takes 7 hours on machine 1, and 1 hour on machine 2, job 2 takes 1 hour on machine 1, and 7 hours on machine 2
        processing_times = np.array([[7,1,3],[1,7,3],[2,2,2],[3,4,5],[1,5,2]])
    
        # We start with only randomly generated patterns.
        # pattern 1 is[[0,7],[7,8]]. The structure is [[start time job 1, start time job 2,...],[compl time job 1, compl time job 2,...]]
        # patterns = [list([[[0, 7, 8], [7, 8, 10]],[[7, 0, 8], [8, 7, 10]]]),
        #             list([[[10, 11, 18], [11, 18, 22 ]],[[10, 11, 18], [11, 18, 22]]])]
    
        patterns = [
                        list(
                                [
                                    [
                                        [0, 7, 8, 10, 13], 
                                        [7, 8, 10, 13, 14],
                                        14
                                    ],
                                    [
                                        [7, 0, 8, 10, 13], 
                                        [8, 7, 10, 13, 14],
                                        14
                                    ]
                                ]
                            ),
                        list(
                                [
                                    [
                                        [0, 7, 8, 10, 14], 
                                        [7, 8, 10, 14, 19],
                                        19
                                    ],
                                    [
                                        [7, 0, 8, 10, 14], 
                                        [8, 7, 10, 14, 19],
                                        19
                                    ]
                                ]
                            ),
                        list(
                                [
                                    [
                                        [0, 3, 6, 8, 13], 
                                        [3, 6, 8, 13, 15],
                                        15
                                    ],
                                    [
                                        [3, 0, 6, 8, 13], 
                                        [6, 3, 8, 13, 15],
                                        15
                                    ]
                                ]
                            )
                  ]



        # # PARAMS
        # n = 5  # number of jobs
        # m = 2  # number of machines
        # # job 1 takes 7 hours on machine 1, and 1 hour on machine 2, job 2 takes 1 hour on machine 1, and 7 hours on machine 2
        # processing_times = np.array([[7,1],[1,7],[2,2],[3,4],[1,5]])
    
        # # We start with only randomly generated patterns.
        # # pattern 1 is[[0,7],[7,8]]. The structure is [[start time job 1, start time job 2,...],[compl time job 1, compl time job 2,...]]
        # # patterns = [list([[[0, 7, 8], [7, 8, 10]],[[7, 0, 8], [8, 7, 10]]]),
        # #             list([[[10, 11, 18], [11, 18, 22 ]],[[10, 11, 18], [11, 18, 22]]])]
    
        # patterns = [
        #                 list(
        #                         [
        #                             [
        #                                 [0, 7, 8, 10, 13], 
        #                                 [7, 8, 10, 13, 14],
        #                                 14
        #                             ],
        #                             [
        #                                 [7, 0, 8, 10, 13], 
        #                                 [8, 7, 10, 13, 14],
        #                                 14
        #                             ]
        #                         ]
        #                     ),
        #                 list(
        #                         [
        #                             [
        #                                 [0, 7, 8, 10, 14], 
        #                                 [7, 8, 10, 14, 19],
        #                                 19
        #                             ],
        #                             [
        #                                 [7, 0, 8, 10, 14], 
        #                                 [8, 7, 10, 14, 19],
        #                                 19
        #                             ]
        #                         ])]
        
        opt = Optimizer(patterns,processing_times,n,m,1)
        solutiondict = opt.test()

### EXPERIMENTS
        # numExp = 5
        # solutionarray = np.zeros(shape=(m+5,numExp))
        # for i in range(numExp):
            
        #     opt = Optimizer(patterns,processing_times,n,m,i+1)
        #     solutiondict = opt.test()
        #     for j in range(m): # get the number of patterns for each machine
        #         solutionarray[j,i] = solutiondict["numPat_m_%s"%j]
        #     solutionarray[m,i] = solutiondict["numInvPricer"]
        #     solutionarray[m+1,i] = solutiondict["numInvBranching"]
        #     solutionarray[m+2,i] = solutiondict["timePricer"]
        #     solutionarray[m+3,i] = solutiondict["timeBranching"]
        #     solutionarray[m+4,i] = i
        
        # # plt.bar(solutionarray[m+4,:],solutionarray[m,:], width = 0.2)
        # # plt.show()
        
        # fig, axs = plt.subplots(3, 2)
        # axs[0, 0].bar(solutionarray[m+4,:],solutionarray[m,:])
        # axs[0, 0].set_title('numInvPricer')
        # axs[0, 1].bar(solutionarray[m+4,:],solutionarray[m+1,:])
        # axs[0, 1].set_title('numInvBranching')
        # axs[1, 0].bar(solutionarray[m+4,:],solutionarray[m+2,:])
        # axs[1, 0].set_title('timePricer[s]')
        # axs[1, 1].bar(solutionarray[m+4,:],solutionarray[m+3,:])
        # axs[1, 1].set_title('timeBranching[s]')
        # width = 0.1
        # for j in range(m):
        #     axs[2, 0].bar(solutionarray[m+4,:]+ j*width,solutionarray[j,:], width = width)

        # axs[2, 0].set_title('numPatPerMach')
        # fig.tight_layout()
        
  
        