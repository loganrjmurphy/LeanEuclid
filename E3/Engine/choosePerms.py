import Levenshtein
import heapq
import json 
import argparse
from itertools import permutations, product 
from dataclasses import dataclass, field

class QuantifierData:
    points : list[str]
    lines : list[str]
    circles : list[str]
    
    def __init__(self, points, lines, circles):
        self.points = points 
        self.lines = lines 
        self.circles = circles

class PropData:
    univNames : QuantifierData
    existNames : QuantifierData

    def __init__(self, univNames, existNames):
        self.univNames = univNames 
        self.existNames = existNames

class PermutationStruct:
    pointPerms : list[list[str]]
    linePerms : list[list[str]]
    circlePerms : list[list[str]]

    def __init__(self,points,lines,circles):
        self.pointPerms=points 
        self.linePerms=lines 
        self.circlePerms=circles
    
    def noPoints(self):
        return self.pointPerms == [()]
    
    def noLines(self):
        return self.linePerms == [()]

    def noCircles(self):
        return self.circlePerms == [()]


def getPermutations(data:QuantifierData):
    return PermutationStruct(list(permutations(data.points)), list(permutations(data.lines)), list(permutations(data.circles)))

@dataclass(order=True)
class NameMap:
    name: list[str] = field(compare=False)
    sim: float

def readNames(data):
    return QuantifierData(points=data["points"], lines=data["lines"], circles=data["circles"])

def readData(inFile):
    permFile = open(inFile, "r")
    props = json.load(permFile)

    reference = props["ground"]
    target = props["guarded_test"]

    groundUnivNames = readNames(props["ground_names"]["univ"])
    groundExistNames = readNames(props["ground_names"]["exist"])

    testUnivNames = readNames(props["guarded_test_names"]["univ"])
    testExistNames = readNames(props["guarded_test_names"]["exist"])

    groundNames = PropData(groundUnivNames,groundExistNames)
    testNames = PropData(testUnivNames,testExistNames)

    return target, reference, groundNames, testNames 

def checkPerm(keys, target, reference, vals):
    subst = target
    mapping = list(zip(keys,vals))
    for key,val in mapping:
        subst = subst.replace(key,val)
    r = Levenshtein.ratio(subst,reference)
    return r

def checkAndInsert(heap, name,N):
    if len(heap) < N:
        heapq.heappush(heap,name)
    else:
        k = heapq.nsmallest(1, heap)
        if k[0] < name:
            heapq.heapreplace(heap,name)

def choosePermutations(ground: PropData, univ : PermutationStruct, exist : PermutationStruct, target, reference,N):
    permHeap = []
    asList = ground.univNames.points + ground.univNames.lines + ground.univNames.circles + ground.existNames.points + ground.existNames.lines + ground.existNames.circles 
    for (uPoints, uLines, uCircles, ePoints, eLines, eCircles) in (product(univ.pointPerms, univ.linePerms, univ.circlePerms, exist.pointPerms, exist.linePerms, exist.circlePerms)):
        perm = uPoints+uLines+uCircles+ePoints+eLines+eCircles
        sim = checkPerm(asList, target, reference,perm)
        x = NameMap(perm, sim)
        checkAndInsert(permHeap,x,N)
    return permHeap, asList

def removeGuards(data) : 
    return list(map(lambda x : x.replace("grd_",""),data))

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--inFile", type=str)
    parser.add_argument("--outFile", type=str)
    parser.add_argument("--N",type=int)
    args = parser.parse_args()
    target, reference, groundNames, testNames = readData(args.inFile)

    univTestPermutaions = getPermutations(testNames.univNames)
    existTestPermutaions = getPermutations(testNames.existNames)
  
    perms, ground = choosePermutations(groundNames, univTestPermutaions, existTestPermutaions, target, reference, args.N)
    
    perms = sorted(perms, reverse = True)
    perms = [list(x.name) for x in perms]
    perms = [removeGuards(x) for x in perms]

    dict = {"ground" : ground, "perms" : perms}
    with open(args.outFile, 'w') as file:
        json.dump(dict, file)

if __name__ == "__main__":
    main()