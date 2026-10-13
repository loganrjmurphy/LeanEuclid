import unittest

from E3.Engine.choosePerms import NameMap, checkAndInsert


class PermutationTests(unittest.TestCase):
    def test_duplicate_mappings_do_not_consume_the_search_budget(self):
        heap = []
        checkAndInsert(heap, NameMap(["a", "b"], 1.0), 3)
        checkAndInsert(heap, NameMap(["a", "b"], 1.0), 3)
        checkAndInsert(heap, NameMap(["b", "a"], 0.9), 3)
        self.assertEqual(len(heap), 2)
        self.assertEqual({tuple(item.name) for item in heap}, {("a", "b"), ("b", "a")})
