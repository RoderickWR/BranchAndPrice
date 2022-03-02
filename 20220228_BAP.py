# -*- coding: utf-8 -*-
"""
Created on Mon Feb 28 22:32:57 2022

@author: WallrathR
"""


from pyscipopt import *
import numpy as np
import inspect


def entering():
    return print("IN ", inspect.stack()[1][3])  # debugging magic


def leaving():
    return print("OUT ", inspect.stack()[1][3])  # debugging magic


class SameDiff(Conshdlr):
    def consdataCreate(self, name, item1, item2, constype, node):
        cons = self.model.createCons(self, name, stickingatnode=True)
        cons.data = {}
        cons.data["item1"] = item1
        cons.data["item2"] = item2
        cons.data["type"] = constype
        cons.data["npropagatedvars"] = 0
        cons.data["npropagations"] = 0
        cons.data["propagated"] = False
        cons.data["node"] = node
        return cons

    def checkVariable(self, cons, var, varid, nfixedvars):
        cutoff = False
        if var.getUbLocal() < 0.5:
            return nfixedvars, cutoff

        constype = cons.data["type"]
        packings = self.model.data["packings"]
        packingId = varid
        existitem1 = packings[packingId][cons.data["item1"]]
        existitem2 = packings[packingId][cons.data["item2"]]

        if (constype == "same" and (existitem1 != existitem2)) or (constype == "diff" and existitem1 and existitem2):
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
        while (v < len(self.model.data["var"])) and (not cutoff):
            nfixedvars, cutoff = self.checkVariable(cons, self.model.data["var"][v], v, nfixedvars)
            v += 1
        if cutoff:
            return {"result": SCIP_RESULT.CUTOFF}
        elif nfixedvars > 0:
            return {"result": SCIP_RESULT.REDUCEDDOM}
        else:
            return result

    def consactive(self, constraint):
        # entering()
        if constraint.data["npropagatedvars"] != len(self.model.data["var"]):
            constraint.data["propagated"] = False
            self.model.repropagateNode(constraint.data["node"])
        # leaving()

    def consdeactive(self, constraint):
        # entering()
        constraint.data["npropagatedvars"] = len(self.model.data["var"])
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
            if not c.data["propagated"]:
                result = self.consdataFixVariables(c, result)
                c.data["npropagations"] += 1
                if result["result"] != SCIP_RESULT.CUTOFF:
                    c.data["propagated"] = True
                    c.data["npropagatedvars"] = len(self.model.data["var"])
                else:
                    leaving()
                    return {"result": SCIP_RESULT.CUTOFF}
        return result


class MyRyanFosterBranching(Branchrule):
    def __init__(self, model):
        self.model = model

    def branchexeclp(self, allowaddcons):
        lpcands, lpcandssol, lpcandsfrac, nlpcands, npriolpcands, nfracimplvars = self.model.getLPBranchCands()

        fractionalities = np.zeros([len(self.model.data["widths"]), len(self.model.data["widths"])])

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

        childsame = self.model.createChild(0.0, self.model.getLocalTransEstimate())

        childdiff = self.model.createChild(0.0, self.model.getLocalTransEstimate())

        conssame = self.model.data["conshdlr"].consdataCreate("some_same_name", row1, row2, "same", childsame)

        consdiff = self.model.data["conshdlr"].consdataCreate("some_diff_name", row1, row2, "diff", childdiff)

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

        integral = lpcands[0]

        self.model.branchVar(integral)

        return {"result": SCIP_RESULT.BRANCHED}


class Pricer(Pricer):
    def addBranchingDecisionConss(self, subMIP, binWidthVars):
        for cons in self.model.data['branchingCons']:
            if (not cons.isActive()):
                continue
            item1 = cons.data['item1']
            item2 = cons.data['item2']

            if cons.data['type'] == 'same':
                subMIP.addCons(binWidthVars[item1] - binWidthVars[item2] == 0)
            elif cons.data['type'] == 'diff':
                subMIP.addCons(binWidthVars[item1] + binWidthVars[item2] <= 1)

    def addFixedVarsConss(self, subMIP, binWidthVars):
        for ii in range(len(self.model.data["var"])):
            if self.model.data["var"][ii].getUbLocal() < 0.5:
                currentPacking = self.model.data["packings"][ii]
                subMIP.addCons(
                    quicksum(w * v for (w, v) in zip(currentPacking, binWidthVars)) <= np.sum(currentPacking) - 1)

    # The reduced cost function for the variable pricer
    def pricerredcost(self):

        # Retrieving the dual solutions
        dualSolutions = []
        for i, c in enumerate(self.data["cons"]):
            dualSolutions.append(self.model.getDualsolLinear(c))
            # dualSolutions.append(self.model.getDualsolSetppc(c))

        #################################################################
        #################################################################

        # Solve the MIP directly

        # Building a MIP to solve the subproblem
        subMIP = Model("BinPacking-Sub")

        # Setting the verbosity level to 0
        subMIP.hideOutput()

        binWidthVars = []
        varNames = []
        varBaseName = "Packing"

        # Variables for the subMIP
        for i in range(len(dualSolutions)):
            varNames.append(varBaseName + "_" + str(i))
            binWidthVars.append(subMIP.addVar(varNames[i], vtype="B", obj=-1.0 * dualSolutions[i]))

        # Adding the knapsack constraint
        subMIP.addCons(
            quicksum(w * v for (w, v) in zip(self.model.data["widths"], binWidthVars)) <= self.model.data["rollLength"])

        # Avoid to generate columns which are fixed to zero
        self.addFixedVarsConss(subMIP, binWidthVars)

        # Add branching decisions constraints to the sub SCIP
        self.addBranchingDecisionConss(subMIP, binWidthVars)

        # Solving the subMIP to generate the most negative reduced cost packing
        subMIP.optimize()

        objval = 1 + subMIP.getObjVal()

        #################################################################
        #################################################################

        # Adding the column to the master problem
        if objval < -1e-08:

            currentNumVar = len(self.model.data["var"])

            # Creating new var; must set pricedVar to True
            newVar = self.model.addVar("NewPacking_" + str(currentNumVar), vtype="I", obj=1.0, pricedVar=True)

            self.model.data["varnames"].append("NewPacking_" + str(currentNumVar))

            # Adding the new variable to the constraints of the master problem
            newPacking = []
            for i, c in enumerate(self.data["cons"]):
                coeff = round(subMIP.getVal(binWidthVars[i]))
                self.model.addConsCoeff(c, newVar, coeff)
                # self.model.addVarBasicSetcover(c, newVar)

                newPacking.append(coeff)

            self.model.data["packings"].append(newPacking)
            self.model.data["var"].append(newVar)

        return {"result": SCIP_RESULT.SUCCESS}

    # The initialisation function for the variable pricer to retrieve the transformed constraints of the problem
    def pricerinit(self):
        for i, c in enumerate(self.data["cons"]):
            self.data["cons"][i] = self.model.getTransformedCons(c)


def test_binpacking():

    master = Model()

    # master.setPresolve(SCIP_PARAMSETTING.OFF)

    master.setIntParam("presolving/maxrestarts", 0)

    master.setParam('limits/time', 30 * 60)

    master.setSeparating(SCIP_PARAMSETTING.OFF)

    # master.setHeuristics(SCIP_PARAMSETTING.OFF)

    master.setObjIntegral()

    pricer = Pricer(priority=5000000)
    master.includePricer(pricer, "BinPackingPricer", "Pricer")
    
    

    conshdlr = SameDiff()

    master.includeConshdlr(
        conshdlr,
        "SameDiff",
        "SameDiff Constraint Handler",
        chckpriority=2000000,
        propfreq=1,
    )

    # my_branchrule = MyRyanFosterBranching(s)

    my_branchrule = MyVarBranching(master)

    master.includeBranchrule(
        my_branchrule,
        "test branch",
        "test branching and probing and lp functions",
        priority=10000000,
        maxdepth=-1,
        maxbounddist=1,
    )

    # item widths
    widths = [
        42, 69, 67, 57, 93, 90, 38, 36, 45, 42, 33, 79, 27, 57, 44, 84, 86, 92, 46, 38, 85, 33, 82, 73, 49, 70, 59, 23,
        57, 72, 74, 69, 33, 42, 28, 46, 30, 64, 29, 74, 41, 49, 55, 98, 80, 32, 25, 38, 82, 30, 35, 39, 57, 84, 62, 50,
        55, 27, 30, 36, 20, 78, 47, 26, 45, 41, 58, 98, 91, 96, 73, 84, 37, 93, 91, 43, 73, 85, 81, 79, 71, 80, 76, 83,
        41, 78, 70, 23, 42, 87, 43, 84, 60, 55, 49, 78, 73, 62, 36, 44, 94, 69, 32, 96, 70, 84, 58, 78, 25, 80, 58, 66,
        83, 24, 98, 60, 42, 43, 43, 39
    ]
    # width demand
    demand = [1] * 120

    # roll length
    rollLength = 150
    assert len(widths) == len(demand)


    #PARAMS 
    n=2 # number of jobs
    m=2 # number of machines
    processing_times = np.array([[7,1],[1,7]]) #job 1 takes 7 hours on machine 1, and 1 hour on machine 2, job 2 takes 1 hour on machine 1, and 7 hours on machine 2


    # We start with only randomly generated patterns.
    # pattern 1 is[[0,7],[7,8]]. The structure is [[start time job 1, start time job 2,...],[compl time job 1, compl time job 2,...]]
    patterns = [{0: [[0,7],[7,8]], 1:[[10,12],[11,19]]},{0: [[0,7],[7,8]], 1:[[10,12],[11,19]] }]

    
    # adding the initial variables
    flowShopVars = []
    varNames = []
    varBaseName = "Pattern"
    packings = []
    lamb = {}
    offset = {}
    s = {}
    f = {}
    alphaCons = {}

    # for i in range(len(widths)):
    #     varNames.append(varBaseName + "_" + str(i))
    #     flowshopVars.append(s.addVar(varNames[i], vtype="B", obj=1.0))
        
    # Create lambda variables for these patterns.
    for i in range(0,m):
        for (key, value) in patterns[i].items():
            lamb[key,i] = master.addVar(vtype="B", name="lambda(%s,%s)"%(key,i)) #is pattern p used on machine i


        offset[i] = master.addVar(vtype="C", name="offset(%s)"%(i),lb =-100.0, ub=100.0)

        for j in range(0,n):
            s[i,j] = master.addVar(vtype="C", name="start(%s,%s)"%(i,j), lb=0.0, ub=100.0)
            f[i,j] = master.addVar(vtype="C", name="finish(%s,%s)"%(i,j), lb=0.0, ub=100.0)
            
            

        alphaCons["convexityOnMachine(%s)"%(i)] = master.addCons( quicksum( lamb[key,i] for (key,value) in patterns[i].items()) - 1 == 0, "convexityOnMachine(%s)"%(i)) # only one pattern per machine
       
            
    #define makespan
    c_max = master.addVar(vtype="C", name="makespan", obj=1.0)
            
    demandCons = []
    for i in range(len(widths)):

        numWidthsPerRoll = 1
        demandCons.append(
            s.addCons(
                numWidthsPerRoll * binpackingVars[i] >= demand[i],
                separate=False,
                modifiable=True,
            ))
        newpacking = [0] * len(widths)
        newpacking[i] = numWidthsPerRoll
        packings.append(newpacking)

    pricer.data = {}

    pricer.data["cons"] = demandCons

    s.data = {}
    s.data["var"] = binpackingVars
    s.data["varnames"] = varNames
    s.data["cons"] = demandCons
    s.data["widths"] = widths
    s.data["demand"] = demand
    s.data["rollLength"] = rollLength
    s.data["packings"] = packings
    s.data["conshdlr"] = conshdlr
    s.data['branchingCons'] = []
    
    s.optimize()

    # print original data
    printWidths = "\t".join(str(e) for e in widths)
    print("\nInput Data")
    print("==========")
    print("Roll Length:", rollLength)
    print("Widths:\t", printWidths)
    print("Demand:\t", "\t".join(str(e) for e in demand))

    # print solution
    widthOutput = [0] * len(widths)
    print("\nResult")
    print("======")
    print("\t\tSol Value", "\tWidths\t", printWidths)
    for i in range(len(s.data["var"])):
        rollUsage = 0
        solValue = s.getVal(s.data["var"][i])
        if solValue > 0:
            outline = "Packing_" + str(i) + ":\t" + \
                str(solValue) + "\t\tCuts:\t "
            for j in range(len(widths)):
                rollUsage += s.data["packings"][i][j] * widths[j]
                widthOutput[j] += s.data["packings"][i][j] * solValue
                outline += str(s.data["packings"][i][j]) + "\t"
            outline += "Usage:" + str(rollUsage)
            print(outline)

    print("\t\t\tTotal Output:\t", "\t".join(str(e) for e in widthOutput))

    print(s.getObjVal())


if __name__ == "__main__":
    test_binpacking()