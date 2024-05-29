import Levenshtein
import heapq
import json
import argparse
from itertools import permutations, product
from dataclasses import dataclass, field
from collections import Counter


def is_permutation(list1, list2):
    return Counter(list1) == Counter(list2)


SHORTCIRCUIT_THRESHOLD = 4000000
SHORTCIRCUIT_SAMPLE_THRESHOLD = 0.88
SHORTCIRCUIT_SAMPLE_CUTOFF = 50


class QuantifierData:
    points: list[str]
    lines: list[str]
    circles: list[str]

    def __init__(self, points, lines, circles):
        self.points = points
        self.lines = lines
        self.circles = circles


def has_permutation(x: QuantifierData, y: QuantifierData):
    return (
        is_permutation(x.points, y.points)
        and is_permutation(x.lines, y.lines)
        and is_permutation(x.circles, y.circles)
    )


class PropData:
    univNames: QuantifierData
    existNames: QuantifierData

    def __init__(self, univNames, existNames):
        self.univNames = univNames
        self.existNames = existNames

    def asList(self):
        return (
            self.univNames.points
            + self.univNames.lines
            + self.univNames.circles
            + self.existNames.points
            + self.existNames.lines
            + self.existNames.circles
        )


def has_match(x: PropData, y: PropData):
    return has_permutation(x.univNames, y.univNames) and has_permutation(
        x.existNames, y.existNames
    )


class PermutationStruct:
    pointPerms: list[list[str]]
    linePerms: list[list[str]]
    circlePerms: list[list[str]]

    def __init__(self, points, lines, circles):
        self.pointPerms = points
        self.linePerms = lines
        self.circlePerms = circles

    def noPoints(self):
        return self.pointPerms == [()]

    def noLines(self):
        return self.linePerms == [()]

    def noCircles(self):
        return self.circlePerms == [()]


def getPermutations(data: QuantifierData):
    return PermutationStruct(
        list(permutations(data.points)),
        list(permutations(data.lines)),
        list(permutations(data.circles)),
    )


@dataclass(order=True)
class NameMap:
    name: list[str] = field(compare=False)
    sim: float

    def __eq__(self, other) -> bool:
        self.name == other.name


def readNames(data):
    return QuantifierData(
        points=data["points"], lines=data["lines"], circles=data["circles"]
    )


def readData(inFile):
    permFile = open(inFile, "r")
    props = json.load(permFile)

    reference = props["ground"]
    target = props["guarded_test"]

    groundUnivNames = readNames(props["ground_names"]["univ"])
    groundExistNames = readNames(props["ground_names"]["exist"])

    testUnivNames = readNames(props["guarded_test_names"]["univ"])
    testExistNames = readNames(props["guarded_test_names"]["exist"])

    groundNames = PropData(groundUnivNames, groundExistNames)
    testNames = PropData(testUnivNames, testExistNames)

    return target, reference, groundNames, testNames


def checkPerm(names, target, reference, guarded):
    subst = target
    mapping = list(zip(guarded, names))
    # print(mapping)
    for key, val in mapping:
        subst = subst.replace(key, val)
    # print(subst,reference)
    r = Levenshtein.ratio(subst, reference)
    return r


def checkAndInsert(heap, name, N):
    if name in heap:
        return ()
    if len(heap) < N:
        heapq.heappush(heap, name)
    else:
        k = heapq.nsmallest(1, heap)
        if k[0] < name:
            heapq.heapreplace(heap, name)


def choosePermutations(
    ground: PropData,
    test: PropData,
    univ: PermutationStruct,
    exist: PermutationStruct,
    target,
    reference,
    N,
):
    short_circuiting = False
    seen_sc = 0
    permHeap = []
    asList = (
        ground.univNames.points
        + ground.univNames.lines
        + ground.univNames.circles
        + ground.existNames.points
        + ground.existNames.lines
        + ground.existNames.circles
    )
    allCombs = product(
        univ.pointPerms,
        univ.linePerms,
        univ.circlePerms,
        exist.pointPerms,
        exist.linePerms,
        exist.circlePerms,
    )

    nonempty_names = []

    if not univ.noPoints():
        nonempty_names += [univ.pointPerms]
    if not univ.noLines():
        nonempty_names += [univ.linePerms]
    if not univ.noCircles():
        nonempty_names += [univ.circlePerms]
    if not exist.noPoints():
        nonempty_names += [exist.pointPerms]
    if not exist.noLines():
        nonempty_names += [exist.linePerms]
    if not exist.noCircles():
        nonempty_names += [exist.circlePerms]

    ceiling = 1
    for x in nonempty_names:
        ceiling *= ceiling * len(x)
    if ceiling > SHORTCIRCUIT_THRESHOLD:
        short_circuiting = True

    if has_match(ground, remove_all_guards(test)):
        print("match found")
        sim = checkPerm(
            ground.asList(), target, reference, replaceGuards(ground.asList())
        )
        checkAndInsert(permHeap, NameMap(ground.asList(), sim), N)

    for uPoints, uLines, uCircles, ePoints, eLines, eCircles in allCombs:
        perm = uPoints + uLines + uCircles + ePoints + eLines + eCircles
        sim = checkPerm(asList, target, reference, perm)
        x = NameMap(perm, sim)
        checkAndInsert(permHeap, x, N)
        if short_circuiting and sim > SHORTCIRCUIT_SAMPLE_THRESHOLD:
            seen_sc += 1
        if short_circuiting and seen_sc >= SHORTCIRCUIT_SAMPLE_CUTOFF:
            return permHeap, asList
    return permHeap, asList


def removeGuards(data):
    return list(map(lambda x: x.replace("grd_", ""), data))


def replaceGuards(data):
    return list(map(lambda x: "grd_" + x, data))


def remove_all_guards(x: PropData):
    univ = QuantifierData(
        removeGuards(x.univNames.points),
        removeGuards(x.univNames.lines),
        removeGuards(x.univNames.circles),
    )
    exist = QuantifierData(
        removeGuards(x.existNames.points),
        removeGuards(x.existNames.lines),
        removeGuards(x.existNames.circles),
    )
    return PropData(univ, exist)


def main():

    parser = argparse.ArgumentParser()
    parser.add_argument("--inFile", type=str)
    parser.add_argument("--outFile", type=str)
    parser.add_argument("--N", type=int)
    args = parser.parse_args()
    target, reference, groundNames, testNames = readData(args.inFile)

    univTestPermutaions = getPermutations(testNames.univNames)

    existTestPermutaions = getPermutations(testNames.existNames)

    perms, ground = choosePermutations(
        groundNames,
        testNames,
        univTestPermutaions,
        existTestPermutaions,
        target,
        reference,
        args.N,
    )

    perms = sorted(perms, reverse=True)
    perms = [list(x.name) for x in perms]
    perms = [removeGuards(x) for x in perms]

    dict = {"ground": ground, "perms": perms}
    with open(args.outFile, "w") as file:
        json.dump(dict, file)


if __name__ == "__main__":
    main()
