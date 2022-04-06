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


def entering():
    return print("IN ", inspect.stack()[1][3])  # debugging magic


def leaving():
    return print("OUT ", inspect.stack()[1][3])  # debugging magic


class SameDiff(Conshdlr):
    def consdataCreate(self, name, item1, item2, constype, node, machineIndex, patternIndex):
        cons = self.model.createCons(self, name, stickingatnode=True)
        cons.data = {}
        cons.data["item1"] = item1
        cons.data["item2"] = item2
        cons.data["type"] = constype
        cons.data["npropagatedvars"] = 0
        cons.data["npropagations"] = 0
        cons.data["propagated"] = False
        cons.data["node"] = node
        cons.data["machineIndex"] = machineIndex
        cons.data["patternIndex"] = patternIndex # which pattern was the branching var chosen from originally
        return cons

    def checkVariable(self, cons, var, varid, nfixedvars):
        cutoff = False
        if var.getUbLocal() < 0.5:
            return nfixedvars, cutoff

        constype = cons.data["type"]
        patterns = self.model.data["patterns"]
        patternId = varid
        existitem1 = patterns[cons.data['machineIndex']][varid][cons.data["item1"]][cons.data["item2"]]


        if (constype == "allowed" and existitem1 == 0) or (constype == "forbidden" and existitem1 == 1):
            print("fixed variable to zero: ", var)
            infeasible, fixed = self.model.fixVar(var, 0.0)
            if infeasible:
                cutoff = True
            else:
                nfixedvars += 1
        return nfixedvars, cutoff


    def consdataFixVariables(self, cons, result):
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

    def consactive(self, constraint):
        # entering()
        if constraint.data["npropagatedvars"] != len(opt.lamb[constraint.data["machineIndex"]]):
            constraint.data["propagated"] = False
            self.model.repropagateNode(constraint.data["node"])
        # leaving()

    # def consdeactive(self, constraint):
    #     # entering()
    #     constraint.data["npropagatedvars"] = len(self.model.data["var"])
    #     # leaving()

    def conscheck(
        self,
        constraints,
        solution,
        checkintegrality,
        checklprows,
        printreason,
        completely,
    ):
        # for cons in constraints:
        #     item1 = cons.data["item1"]
        #     item2 = cons.data["item1"]
        #     packings = self.model.data["packings"]
        #     for i in range(len(self.model.data["var"])):
        #         sol = solution[self.model.data["var"][i]]
        #         if sol < 0.5:
        #             continue
        #         else:
        #             packingId = i
        #             existitem1 = packings[packingId][item1]
        #             existitem2 = packings[packingId][item2]
        #             if cons.data['type'] == 'same' and existitem1 != existitem2:
        #                 return {"result": SCIP_RESULT.INFEASIBLE}
        #             elif cons.data['type'] == 'diff' and existitem1 and existitem2:
        #                 return {"result": SCIP_RESULT.INFEASIBLE}

        return {"result": SCIP_RESULT.FEASIBLE}

    def consenfolp(self, constraints, nusefulconss, solinfeasible):
        pass

    def consenfops(self, constraints, nusefulconss, solinfeasible, objinfeasible):
        pass

    def consprop(self, constraints, nusefulconss, nmarkedconss, proptiming):
        result = {"result": SCIP_RESULT.DIDNOTFIND}
        for c in constraints:
            print("c.data", c.data)
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


class MyRyanFosterBranching(Branchrule):
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

    def branchexeclp(self, allowaddcons):

        (
            lpcands,
            lpcandssol,
            lpcandsfrac,
            nlpcands,
            npriolpcands,
            nfracimplvars,
        ) = self.model.getLPBranchCands()

        integral = lpcands[0] #take the first candidate
        
        patternInd = [int(s) for s in re.findall(r'\b\d+\b', integral.name)] #which pattern is meant by the lambda variable
        
        pattern = patterns[patternInd[0]][patternInd[1]] #retrieve the corresponding pattern, ind[0] is the machine, ind[1] the pattern
        
        pricing = list(self.model.data["pricer"].pricingList.items())[patternInd[0]][1] #get the corresponding pricing problem NOT USED
    
            
        childsmaller = self.model.createChild(
            0.0, self.model.getLocalEstimate())

        childbigger = self.model.createChild(
            0.0, self.model.getLocalEstimate())

        conssmaller = self.model.data["conshdlr"].consdataCreate(
            "some_allowed_name", random.randint(0,3), random.randint(0,3), "allowed", childsmaller, patternInd[0], patternInd[1])

        consbigger = self.model.data["conshdlr"].consdataCreate(
            "some_forbidden_name", random.randint(0,3), random.randint(0,3), "forbidden", childbigger, patternInd[0], patternInd[1])
        print("created 2 new nodes")
        self.model.addConsNode(childsmaller, conssmaller)

        self.model.addConsNode(childbigger, consbigger)

        self.model.data['branchingCons'].append(conssmaller)

        self.model.data['branchingCons'].append(consbigger)

        return {"result": SCIP_RESULT.BRANCHED}

# Pricing creates one pricing problem. You need to provide the processing times matrix, the machine index, and the dual information to form the objective
class Pricing:

    def __init__(self, initProcessingTimes, i, n, omega):
        self.n = n
        self.s = {}
        self.f = {}
        self.x = {}
        self.processing_times = initProcessingTimes
        self.machineIndex = i
        self.bigM = 100
        self.pricing = Model()
        # self.beta = beta
        # self.gamma = gamma
        self.omega = omega
        self.createPricing()

    def createPricing(self):

        # 2) CREATE PRICING

   
        # self.pricing.params.outputflag = 0
        # self.pricing.modelSense = GRB.MINIMIZE

        for j in range(0, self.n):
            self.s[j] = self.pricing.addVar(
                vtype="C", name="start(%s)" % (j), lb=0.0, ub=100.0)
            self.f[j] = self.pricing.addVar(
                vtype="C", name="finish(%s)" % (j), lb=0.0, ub=100.0)

        # Create order matrix
        for k in range(0, self.n):
            for j in range(0, self.n):
                if k != j:
                    self.x[k, j] = self.pricing.addVar(
                        vtype="B", name="x(%s,%s)" % (k, j), obj = -1.0 * self.omega["%s%s"%(k,j)])        
                else:
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
                
        
        
# Pricer is the pricer plugin from pyscipopt. In the reduced costs function new patterns will be generated during BAP
class Pricer(Pricer):
    def addBranchingDecisionConss(self, modelIN, machineIndex):
        for cons in self.model.data['branchingCons']:
            if (not cons.isActive()):
                continue
            item1 = cons.data['item1']
            item2 = cons.data['item2']

            if cons.data['type'] == 'allowed':
                modelIN.pricing.addCons(modelIN.x[item1,item2] == 1, "allowOrder(%s%s)"%(item1,item2))

            elif cons.data['type'] == 'forbidden':
                modelIN.pricing.addCons(modelIN.x[item1,item2] == 0, "forbiddenOrder(%s%s)"%(item1,item2))

    def addFixedVarsConss(self, modelIN, machineIndex):
        ind = 0
        # for i in self.model.data["lamb"][machineIndex]:
        #     # print("getUBLocal", i.getUbLocal())
        #     if i.getUbLocal() < 0.5:
        #         modelIN.pricing.addCons(quicksum(quicksum(modelIN.x[k,j] for j in range(4) if k != j and self.model.data["patterns"][machineIndex][ind][k][j] == 1) for k in range(4))  <= np.sum(self.model.data["patterns"][machineIndex][ind]) - self.model.data["patterns"][machineIndex][ind][0][0] - self.model.data["patterns"][machineIndex][ind][1][1] - self.model.data["patterns"][machineIndex][ind][2][2] - self.model.data["patterns"][machineIndex][ind][3][3] - 1, "NoPat(%s)_m%s"%(i,machineIndex))
        #     ind += 1

    # The reduced cost function for the variable pricer
    def pricerredcost(self):

        # Retrieving the dual solutions
        dualSolutionsAlpha = []
        # dualSolutionsBeta = []
        # dualSolutionsGamma = []
        dualSolutionsOmega = {}
        
        for i, c in enumerate(self.data["alphaCons"]):
            dualSolutionsAlpha.append(self.model.getDualsolLinear(c))
        #     # dualSolutions.append(self.model.getDualsolSetppc(c))
        # for i, c in enumerate(self.data["betaCons"]):
        #     dualSolutionsBeta.append(self.model.getDualsolLinear(c))
        # for i, c in enumerate(self.data["gammaCons"]):
        #     dualSolutionsGamma.append(self.model.getDualsolLinear(c))
        for i in range(self.data["m"]):
            dualSolutionsOmega[i] = {}
            for (key,value) in self.data["omegaCons"][i].items():
                dualSolutionsOmega[i][key] = self.model.getDualsolLinear(value)
                

              
        # create pricing list using the current dual information from the master
        self.pricingList = self.createPricingList(dualSolutionsOmega)  # a list of m pricing problems
        
        # counts pricing problems that cannot find negative reduced costs
        nbrPricingOpt = 0

        # iterate through the pricing list
        for i, (key, pricing) in enumerate(self.pricingList.items()):
            
            
            # Avoid to generate columns which are fixed to zero
            self.addFixedVarsConss(pricing, i)
            
            # Add branching decisions constraints to the sub SCIP
            self.addBranchingDecisionConss(pricing, i)
            
            pricing.pricing.optimize()
            
            #check negative reduced costs
            if opt.bigM + pricing.pricing.getObjVal() - dualSolutionsAlpha[i] < -1e-10:
                
              print("Reduced costs of pricing ", i, "is ", 100 + pricing.pricing.getObjVal() - dualSolutionsAlpha[i]  )  
              
              # retrieve pattern with negative reduced cost
              newPattern = self.retrieveXMatrix(pricing)
              
              opt.master.data["patterns"][i][len(opt.master.data["patterns"][i])] = newPattern
              print("pattern ", newPattern, " is added for machine " , i )

              # create new lambda variable for that pattern
              newVar = opt.master.addVar(vtype="B", pricedVar=True, name = "lamb_m(%s)p(%s)"%(i,len(opt.master.data["patterns"][i]) - 1))
              
              # add the lambda variable to the master
              opt.master.data["lamb"][i].append(newVar)
              
              
              # add the new variable to the master constraints for machine i
              opt.master.addConsCoeff(opt.master.data["alphaCons"][i], newVar, 1)
              
              # for ind, c in enumerate(self.data["betaCons"][i*opt.numberJobs:(i+1)*opt.numberJobs]):
              #     opt.master.addConsCoeff(c, newVar, newPattern[0][ind - i*opt.numberJobs])
                  
              # for ind, c in enumerate(self.data["gammaCons"][i*opt.numberJobs:(i+1)*opt.numberJobs]):
              #     opt.master.addConsCoeff(c, newVar, newPattern[1][ind - i*opt.numberJobs])
              
              for (key,value) in opt.master.data["omegaCons"][i].items():
                  # print("key", key)
                  # print("value", value)
                  # print("newPattern[int(key[0])][int(key[1])]",newPattern[int(key[0])][int(key[1])])
                  opt.master.addConsCoeff(value, newVar, newPattern[int(key[0])][int(key[1])]*opt.bigM)
   
            # increment counter if machine i does not find any new patterns with negative reduced costs      
            if opt.bigM + pricing.pricing.getObjVal() - dualSolutionsAlpha[i] >= -1e-10:
              nbrPricingOpt += 1
       
        print("pricing done")    
        return {"result": SCIP_RESULT.SUCCESS}
    
    # retrieve a pattern from modelIN
    def retrieveXMatrix(self,pricerIN):
        matrix = np.zeros((self.data["n"],self.data["n"]))
        mat = []
        mat = [[pricerIN.pricing.getVal(pricerIN.x[0,j]) for j in range(0,self.data["n"])],[pricerIN.pricing.getVal(pricerIN.x[1,j]) for j in range(0,self.data["n"])],[pricerIN.pricing.getVal(pricerIN.x[2,j]) for j in range(0,self.data["n"])],[pricerIN.pricing.getVal(pricerIN.x[3,j]) for j in range(0,self.data["n"])]]
        
        return mat  
    
    def createPricingList(self, dualSolutionsOmega):
        # PARAMS
        # job 1 takes 7 hours on machine 1, and 1 hour on machine 2, job 2 takes 1 hour on machine 1, and 7 hours on machine 2
        pricingList = {}
        for i in range(0, opt.numberMachines):
            pricing = Pricing(opt.processing_times, i, opt.numberJobs, dualSolutionsOmega[i])
            pricingList["pricing(%s)" % i] = pricing
    
        return pricingList
    
    # The initialisation function for the variable pricer to retrieve the transformed constraints of the problem
    def pricerinit(self):
        for i, c in enumerate(self.data["alphaCons"]):
            self.data["alphaCons"][i] = self.model.getTransformedCons(c)
        # for i, c in enumerate(self.data["betaCons"]):
        #     self.data["betaCons"][i] = self.model.getTransformedCons(c)
        # for i, c in enumerate(self.data["gammaCons"]):
        #     self.data["gammaCons"][i] = self.model.getTransformedCons(c)
        for i in range(self.data["m"]):
            for (key,value) in self.data["omegaCons"][i].items():
                self.data["omegaCons"][i][key] = self.model.getTransformedCons(value)
            #     print("self.model.getDualsolLinear(self.data['omegaCons][i])", self.model.getDualsolLinear(self.data["omegaCons"][i]))
        # print("done")
    


# In Optimizer, (1) the master problem and the flow shop parameters are defined, (2) the BAP algorithm is configured and executed, (3) the Gantt is drawn
class Optimizer: 
    
    def __init__(self,initPatterns,initProcessingTimes,n,m): 
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
                self.lamb[i].append(self.master.addVar(vtype="B", name = "lamb_m(%s)p(%s)"%(i,l) ))  # is pattern p used on machine i
            self.offset.append(self.master.addVar(vtype="C", name = "offset_m%s"%i )) 
    
            for j in range(0, self.numberJobs):
                self.s.append(self.master.addVar(vtype="C", name = "start_m(%s)j(%s)"%(i,j)))
                self.f.append(self.master.addVar(vtype="C", name = "finish_m(%s)j(%s)"%(i,j)))
    
            self.alphaCons.append(self.master.addCons(quicksum( self.lamb[i][l] for l in range(len(self.patterns[i]))) - 1 == 0, "convexityOnMachine(%s)" % (i), separate=False, modifiable=True))  # only one pattern per machine
    
        # define makespan
        c_max = self.master.addVar(vtype="C", name="makespan", obj=1.0)
    
        for i in range(0, self.numberMachines):
            self.omegaCons[i] = {}
            for k in range(0,self.numberJobs):
                for j in range(0,self.numberJobs):
                    if k != j:
                        self.omegaCons[i]["%s%s"%(k,j)] = self.master.addCons(self.f[k + i*self.numberJobs] - self.s[j + i*self.numberJobs] - self.bigM*(1-quicksum(self.patterns[i][l][k][j]*self.lamb[i][l] for l in range(len(self.patterns[i]))) ) <=  0, "finishStart(%s,%s,%s)"%(i,k,j), separate=False, modifiable=True) # for each job k the finishing date one machine i has to be smaller than the starting date of the next job j, (1) if j follows k on i, (2) if job k was not the cutoff job (last job) on i 
        #     for j in range(0, self.numberJobs):
        #         self.betaCons.append(self.master.addCons(quicksum( self.patterns[i][l][0][j]* self.lamb[i][l] for l in range(len( self.patterns[i]))) +
        #                                                            self.offset[i] -  self.s[j + i* self.numberJobs] == 0, separate=False, modifiable=True, name = "startCon_m(%s)j(%s)" %(i,j))) # starting time on machine i for job j is determined by the starting time of job j in the selected pattern p
        #         # completion time on machine i for job j is determined by the completion time of job j in the selected pattern p
        #         self.gammaCons.append(self.master.addCons(quicksum( self.patterns[i][l][1][j]* self.lamb[i][l] for l in range(len( self.patterns[i]))) +  self.offset[i] -  self.f[j + i* self.numberJobs] == 0, separate=False, modifiable=True, name = "finishCon_m(%s)j(%s)" %(i,j)))
            if i !=  self.numberMachines-1:
                for j in range(0, self.numberJobs):
                    self.master.addCons( self.f[j + i*self.numberJobs] <=  self.s[j + (i+1)*self.numberJobs],
                                   "interMachine(%s,%s)" % (i, j))
            for j in range(0, self.numberJobs):
                self.master.addCons( self.s[j + i*self.numberJobs] +  self.processing_times[j, i] ==  self.f[j + i* self.numberJobs],
                               "startFinish(%s,%s)" % (i, j))
    
        for j in range(0, self.numberJobs):
            self.master.addCons(c_max >=  self.f[j + ( self.numberMachines-1)* self.numberJobs], "makespanConstrMachine(%s)" % (j))
            
        #### End         
    
            
        pricer.data = {}
        pricer.data["alphaCons"] =  self.alphaCons
        # pricer.data["betaCons"] =  self.betaCons
        # pricer.data["gammaCons"] =  self.gammaCons
        pricer.data["omegaCons"] =  self.omegaCons
        pricer.data["m"] =  self.numberMachines
        pricer.data["n"] =  self.numberJobs
    
        self.master.data = {}
        self.master.data["s"] =  self.s
        self.master.data["f"] =  self.f
        self.master.data["offset"] =  self.offset
        self.master.data["lamb"] =  self.lamb
        self.master.data["alphaCons"] =  self.alphaCons
        # self.master.data["betaCons"] =  self.betaCons
        # self.master.data["gammaCons"] =  self.gammaCons
        self.master.data["omegaCons"] =  self.omegaCons
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


if __name__ == "__main__":
    
        # PARAMS
        n = 4  # number of jobs
        m = 2  # number of machines
        # job 1 takes 7 hours on machine 1, and 1 hour on machine 2, job 2 takes 1 hour on machine 1, and 7 hours on machine 2
        processing_times = np.array([[7,1],[2,3],[1,7],[6,10]])
    
        # We start with only randomly generated patterns.
        # pattern 1 is[[0,7],[7,8]]. The structure is [[start time job 1, start time job 2,...],[compl time job 1, compl time job 2,...]]
        # patterns = [list([[[0, 7, 8], [7, 8, 10]],[[7, 0, 8], [8, 7, 10]]]),
        #             list([[[10, 11, 18], [11, 18, 22 ]],[[10, 11, 18], [11, 18, 22]]])]
    
        patterns = [
                        {0: 
                             [
                                 [0,1,1,1],
                                 [0,0,1,1],
                                 [0,0,0,1],
                                 [0,0,0,0]
                             ], 
                         1:
                             [
                                 [0,0,0,0],
                                 [0,0,1,1],
                                 [0,0,0,1],
                                 [0,1,1,1]
                             ] 
                        }, 
                        {0:
                             [
                                 [0,1,1,1],
                                 [0,0,1,1],
                                 [0,0,0,1],
                                 [0,0,0,0]
                             ], 
                         1:
                             [
                                 [0,0,0,0],
                                 [0,0,1,1],
                                 [0,0,0,1],
                                 [0,1,1,1]
                             ] 
                        }
                 ]

        opt = Optimizer(patterns,processing_times,n,m)
        opt.test()
