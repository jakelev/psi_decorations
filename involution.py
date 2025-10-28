#from sage.graphs.independent_sets import IndependentSets
from collections import Counter
from itertools import accumulate, product
from basics import *

class MismatchedDecoration:
    """
    The core class: a MismatchedDecoration for a psi class product. This is defined by some auxiliary data:
    - self.color_counts (list Int):         Count of marked points in each color
    - self.exponents (list (list Int)):     List of strictly-positive exponents in each color (or [] for no exponents in a color).
                                              Usually, exponents should be in increasing order within each color.
                                              Explicitly include empty lists for colors with no nonzero exponents.
                                              This is the number of "boxed entries" in each row.
    - self.hues (list (list Int)):          List of hue partitions, one per color: a set partition of 0, ..., k-1,
                                              where k is the number of boxed points (i.e. with a nonzero exponent) of that color.
    - dec (dict: (Int, Int) -> (Int, Int)): The decoration itself, assigning each marked point a "hue" (minimal element of a hue partition block).
                                              See rules below.
    - print_mode:                           Whether to display marked points as ordered pairs (color index, point index) or as single numbers.
                                              Options are 'pairs' and 'ordered'.
    - index_print_mode:                     Whether to display ordered marked points as zero-indexed or one-indexed.
                                              Options are 0, 1.

    Rules:
        - Marked points are represented internally as zero-indexed ordered pairs (color index, point index).
          For example, the first marked point of the first color is (0, 0). However, they can be printed as numbered points from 1...N by setting
          print_mode='ordered' and index_print_mode=1.
        - In the decoration:
            1. dec[0, 0] == dec[1, 0] == dec[2, 0] == (None, None) (cross out the first point in each of the first three colors)
            2. Within each non-singleton hue block, every non-minimal element has dec[c, i] == the minimum of its block.
            3. The "unboxed" entries have dec[c, i] == (d, j) where d != c and (d, j) is a minimum of a hue block.
            4. The number of times a given hue (d, j) occurs as a value of dec is the sum of the exponents on that block.
    
    See the alternate constructor function MDOrdered() below, which is for inputting the hues and decoration with
    marked points labeled 1, ..., N rather than as ordered pairs.

    Other functionality:
        - Pretty printing: if MD is a MismatchedDecoration, print(MD) prints it nicely.
        - Auxiliary built-in constants:
            self.total_points               (Int)
            self.num_colors                 (Int)
            self.partial_sums               (list Int) starting with 0, the partial sums of colors.
            self.num_nonzero_exps_by_color  (list Int)
            self.total_exps_by_color        (list Int)
            self.mins_of_hues               (list (list Int))
            self.total_exponents_by_hues    (list (list Int))
        - Built-in functions:
            self.sign()                     (returns Int) the sign := the number of underlined boxed entries
            self.__eq__(other)              (returns Bool) two MismatchedDecorations are equal if they have equal
                                                           color_counts, exponents, hues and decoration.
            self.chain_decompositions()     Returns the number and hue chain decompositions.
                                            With optional argument return_start_idx_of_chains=True, also returns the indices
                                            pointing to the starts of the chains.
            self.find_permissions()         Returns the candidates and targets with "permission to merge" in the sense of the hue involution.
    """
    def __init__(self, color_counts, exponents, hues, dec, print_mode='pairs', index_print_mode=0):

        self.print_mode = print_mode
        self.index_print_mode = index_print_mode
        
        # Validate color_counts is a list of ints
        if not (isinstance(color_counts, list) and len(color_counts) >= 3 and
                all((isinstance(x, int) and x > 0) for x in color_counts)):
            raise TypeError("color_counts must be a list of at least 3 positive ints")
        
        self.color_counts = [c for c in color_counts]
        self.total_points = sum(self.color_counts)
        self.num_colors = len(self.color_counts)
        self.partial_sums = [0] + list(accumulate(self.color_counts))
        
        # Validate exponents is a list of lists of ints
        if not (isinstance(exponents, list) and 
                all(isinstance(sublist, list) and all((isinstance(k, int) and k > 0) for k in sublist) for sublist in exponents)):
            raise TypeError("exponents must be a list of lists of positive ints")
            
        self.exponents = [[e for e in sublist] for sublist in exponents]
        self.num_nonzero_exps_by_color = [len(exps_by_color) for exps_by_color in self.exponents]
        self.total_exps_by_color = [sum(exps_by_color) for exps_by_color in self.exponents]
        self.total_exp = sum(self.total_exps_by_color)
        
        if not(self.total_exp + 3 == self.total_points):
            raise ValueError("exponents must add up to number of points minus 3")

        # Validate hues is a list of lists of lists of ints
        if not (isinstance(hues, list) and 
                all(isinstance(outer, list) and 
                    all(isinstance(inner, list) and 
                        all(isinstance(x, int) for x in inner) for inner in outer) for outer in hues)):
            raise TypeError("hues must be a list of lists of lists of ints")
        
        self.hues = [sorted([sorted([h for h in hue]) for hue in hue_partition]) for hue_partition in hues]
        self.mins_of_hues = [[min(hue) for hue in hue_partition] for hue_partition in self.hues]
        self.total_exponents_by_hues = [[sum(exps_by_color[i] for i in part) for part in hue_partition]
                                        for (hue_partition, exps_by_color) in zip(self.hues, self.exponents)]
        
        # Validate that each part of hues is a set partition of the points of that color with nonzero exponents
        if not(len(self.hues) == self.num_colors):
            raise ValueError("provide one hue partition for each color")
        if not(all(is_partition_of(hue_partition, ell) for (hue_partition, ell) in zip(self.hues, self.num_nonzero_exps_by_color))):
            raise ValueError("each hue partition must be a set partition of the nonzero exponents in that color")
        
        # Validate dec is a dict
        # each key of dec should be a pair (color, index) and the value should be the minimum element of a hue.
        if not isinstance(dec, dict):
            raise TypeError("dec must be a dict")
        
        # Check that unboxed entries are mismatched
        self.dec = dec.copy()
        self._check_mismatched()
    
    def _format_pair(self, p):
        """Helper method to format a point indexed p = (color, index) for display"""
        if self.print_mode == 'pairs':
            if p == (None, None):
                return '(-, -)'
            return str((p[0] + self.index_print_mode, p[1] + self.index_print_mode))
        if p == (None, None):
            return '--'
        i = self.partial_sums[p[0]] + p[1]
        return str(i + self.index_print_mode).rjust(2)
    
    def _check_mismatched(self):
        for (c, (LH, LC)) in enumerate(zip(self.num_nonzero_exps_by_color, self.color_counts)):
            for i in range(LC):
                p = (c, i)
                h = self.dec[p]
                if c < 3 and i == 0:
                    if h != (None, None):
                        raise ValueError(f"Entry should be crossed out but has a hue: "
                                        f"{self._format_pair(p)}: {self._format_pair(h)}")
                elif (not 0 <= h[0] < self.num_colors) or (h[1] not in self.mins_of_hues[h[0]]):
                    raise IndexError(f"Invalid hue assignment (out of range or not a minimum of a hue): "
                                     f"{self._format_pair(p)}: {self._format_pair(h)}")
                if i < LH and i not in self.mins_of_hues[c]:
                    # p must be labeled by its own block
                    # find block containing i in color c
                    if h[0] != p[0] or h[1] != [min(hue) for hue in self.hues[c] if i in hue][0]:
                        raise ValueError(f"A boxed underlined entry was not assigned its own block as its hue:"
                                         f"{self._format_pair(p)}: {self._format_pair(h)}")
                if i >= LH and h[0] == c:
                    raise ValueError(f"An unboxed entry has a hue matching its color: "
                                     f"{self._format_pair(p)}: {self._format_pair(h)}")
        
        # Check that the decoration counts match with the hue totals
        self.dec_counter = Counter(self.dec.values())
        if not(all(self.dec_counter[c, hmin] == hcount
                   for c in range(self.num_colors) for hmin, hcount in zip(self.mins_of_hues[c], self.total_exponents_by_hues[c]))):
            raise ValueError("decoration counts do not match hue totals")
    
    def sign(self):
        """The sign of the mismatched decoration."""
        # number of underlined entries
        # aka sum of (hue-1) over all hues.
        # know: sum of (hue) = n, total number of points.
        return (-1) ** sum(sum(len(hue)-1 for hue in hue_partition) for hue_partition in self.hues)
    
    def __str__(self):
        """Return a readable string representation of the MismatchedDecoration object"""
        return (
            f"MismatchedDecoration(\n"
            f"  color_counts={{self.color_counts}},\n"
            f"  exponents={{self.exponents}},\n"
            f"  hue partition for each color:\n    {{self._format_hues()}},\n"
            f"  decoration=\n    {{self._format_dec()}}\n"
            f")"
        )
    def __eq__(self, other):
        if not isinstance(other, MismatchedDecoration):
            return False
        
        return all([self.color_counts == other.color_counts,
                    self.exponents == other.exponents,
                    self.hues == other.hues,
                    self.dec == other.dec])
    
    def _format_hues(self):
        """Helper method to format hue partitions for display"""
        if self.print_mode == "pairs":
            return '\n    '.join(str([[i + self.index_print_mode for i in h] for h in hue_partition]) for hue_partition in self.hues)
        
        # for totally ordered numbers
        rows = []
        for c, hue_partition in enumerate(self.hues):
            rows.append('[' + ', '.join('[' + ', '.join(self._format_pair((c, i)) for i in hue) + ']' for hue in hue_partition) + ']')
        return '\n    '.join(rows)
    
    def _format_dec(self):
        """Helper method to format decoration for display"""        
        rows = []
        
        if self.print_mode == "pairs":
            pad = 17
        else:
            pad = 9
        
        for (c, (LH, LC)) in enumerate(zip(self.num_nonzero_exps_by_color, self.color_counts)):
            row = [f"[{self._format_pair((c, i))} : {self._format_pair(self.dec[c, i])}]".ljust(pad) for i in range(LH)] +\
                [f" {self._format_pair((c, i))} : {self._format_pair(self.dec[c, i])} ".ljust(pad) for i in range(LH, LC)]
            rows.append(', '.join(row))
        return '\n    '.join(rows)

    def chain_decomposition(self, c, return_start_idx_of_chains=False):
        """Return the number and hue chain decompositions in color c, and (optionally)
             the indices of the starts of the chains.
        
        Note: the number and hue chain are NOT lists of ordered pairs, but lists of zero-indexed indices within the color c.
        Thus, an output integer i corresponds to the marked point (c, i).
        """
        if not 0 <= c < self.num_colors:
            raise ValueError("color index out of range")
        
        # The pairs (number, hue) of non-crossed-out, non-underlined entries, whose hues match the color c
        pairs = [(m, self.dec[c, m]) for m in self.mins_of_hues[c]]
        pairs = [(m, h[1]) for m, h in pairs if h != (None, None) and h[0] == c]
        if len(pairs) == 0:
            if return_start_idx_of_chains:
                return [], [], []
            return [], []
        numbers, hues = zip(*pairs)
        numbers, hues = list(numbers), list(hues)
        
        # form the number chain
        number_chain_decomposition = []
        hue_chain_decomposition = []
        start_idx_of_chains = []
        while len(numbers) > 0:
            try:
                i_new = hue_chain_decomposition[-1] # most recent hue
                next = numbers.index(i_new) # try to find i_new in remaining list of numbers
            except (IndexError, ValueError): # fails at first step, or if i_new is not in the remaining list
                next = numbers.index(min(numbers)) # by default, take the next smallest remaining number
                start_idx_of_chains.append(len(number_chain_decomposition)) # remember that this index is the start of new chain
                
            # pop entry from numbers, hues lists and store in the chain
            number_chain_decomposition.append(numbers.pop(next))
            hue_chain_decomposition.append(hues.pop(next))
        
        if return_start_idx_of_chains:
            return number_chain_decomposition, hue_chain_decomposition, start_idx_of_chains    
        return number_chain_decomposition, hue_chain_decomposition

    def find_permissions(self):
        """Find all t = (c, i) with permission to merge.
        
        Returns: (list of candidates t, list of merge targets r)."""

        candidates = []
        permissions = []
        
        # all underlined boxed entries (i.e. not minima of hue blocks)
        skip = [self.partial_sums[c] + i
                for c in range(self.num_colors)
                for i in range(self.num_nonzero_exps_by_color[c]) if i not in self.mins_of_hues[c]]

        for c in range(self.num_colors):
            # skip any color with no boxed entries
            if self.num_nonzero_exps_by_color[c] == 0:
                continue

            # we will need the number and hue chain decompositions and chain start indices
            number_chain_decomposition, hue_chain_decomposition, start_idx_of_chains =\
                self.chain_decomposition(c, return_start_idx_of_chains=True)
            
            # examine all singleton blocks of color c
            for t in [hue[0] for hue in self.hues[c] if len(hue) == 1]:
                # NOTATIONAL WARNING: t is not a pair, it is just the within-color index

                # find first occurrence of t in the hue chain decomposition
                try:
                    h_idx = hue_chain_decomposition.index(t)
                except ValueError: # nothing has hue i!
                    # print(f"nothing has this hue")
                    continue
                r = number_chain_decomposition[h_idx] # r has hue t

                # check for q: if r is not the start of a chain, q is the thing before it
                if h_idx not in start_idx_of_chains:
                    q = number_chain_decomposition[h_idx - 1]
                    skip.append(self.partial_sums[c] + q)

                if r <= t:
                    # print(f"{D.partial_sums[c]+r+1} has this hue, but this is not a clinging")
                    continue # not clinging!
                # print(f"t={D.partial_sums[c]+t+1} is clinging to r={D.partial_sums[c]+r+1}")
                skip.append(self.partial_sums[c] + r) # skip this index when checking remaining hues below
                
                
                # check remainder of decoration: except at q, r, all other instances of hue (c, r) precede (c, t)
                # form list excluding (c, q), (c, r)

                permission_list_order = [self.dec[c, ii] for ii in number_chain_decomposition
                                        if self.partial_sums[c] + ii not in skip]
                
                rest_of_list = [self.dec[cc, ii]
                                for cc in range(self.num_colors)
                                for ii in range(self.color_counts[cc])
                                if cc != c and self.dec[cc, ii][0] == c]

                checklist = permission_list_order + rest_of_list
                
                # bad: if there is a (c, t) and then a (c, r)
                try:
                    first_c_t = checklist.index((c, t))
                    _ = checklist[first_c_t:].index((c, r))
                except ValueError:
                    candidates.append((c, t)) # permission! we did not find a counterexample
                    permissions.append((c, r))
            # finished testing t
        # finished testing color c

        return candidates, permissions

def MDOrdered(color_counts, exponents, hues, dec, index_mode=0):
    """Constructor for a mismatched decoration in which the hues and decoration are given
         in total order rather than as pairs.
       Also, index_mode=1 allows for the hues and dec to be inputted as one-indexed, i.e. marked points numbers 1, ..., N.
         (Internally the representation remains zero-indexed and by pairs.)

        See the main MismatchedDecoration class for rules.
    """
    enum_partial_sums = list(enumerate(accumulate(color_counts, initial=0))) # [(0, 0), (1, c1), (2, c1+c2), (3, c1+c2+c3), ...]
    def _to_pair(p):
        if p is None:
            return (None, None)
        c = next(i-1 for i, s in enum_partial_sums if s > p - index_mode)
        return (c, p - index_mode - enum_partial_sums[c][1])
    
    new_hues = [[[_to_pair(h)[1] for h in hue] for hue in hue_partition] for hue_partition in hues]
    new_dec = {_to_pair(key):_to_pair(dec[key]) for key in dec}
    
    return MismatchedDecoration(color_counts, exponents, new_hues, new_dec, print_mode="ordered", index_print_mode=index_mode)

def hue_involution(D):
    """The sign-reversing involution on mismatched decorations. See paper for definition.
    
    Input:
        D:   a MismatchedDecoration
    Returns: D, or a MismatchedDecoration with the opposite sign.
    """
    
    infinity = (D.num_colors, 0) # larger than any pair (c, i)

    # compute m: minimum element of first non-singleton hue block
    m = min(((c, min(h))
             for c, hue_partition in enumerate(D.hues)
             for h in hue_partition if len(h) > 1), default=infinity)
    
    # compute t
    candidates, permissions = D.find_permissions()
    t = infinity
    if len(candidates) > 0:
        t, r = candidates[0], permissions[0]
    
    if t == infinity and m == infinity:
        # fixed point!
        return D

    # will become the new list of hue partitions
    new_hues = [[[h for h in hue] for hue in hue_partition] for hue_partition in D.hues]

    if m < t:
        # m wins (split case), necessarily m is not infinity

        c = m[0] # the color where the split takes place
        
        # correct the new list of hues
        B_idx = D.mins_of_hues[c].index(m[1]) # find old block whose min is m
        old_block = new_hues[c].pop(B_idx) # delete it
        new_hues[c] += [old_block[:1], old_block[1:]] # split it into two blocks
        new_hues[c] = sorted(new_hues[c]) # sort those blocks

        # correct the decoration
        new_dec = D.dec.copy()
        r = (c, old_block[1])
        # desired multiplicities of new labels
        r_mult = D.total_exponents_by_hues[c][B_idx] - D.exponents[c][m[1]]
        m_mult = D.exponents[c][m[1]] #(technically unnecessary to track, just a sanity check)

        # Step 1: Relabel the minimum of the new block as m
        new_dec[r] = m
        m_mult -= 1
        skips = [r] # entries to skip in step 4

        # Step 2: Relabel all other elements of the new block as that block (i.e. as its minimum element, which is r)
        for i in old_block[2:]:
            new_dec[c, i] = r
            r_mult -= 1
            skips.append((c, i))


        # Step 3: check if "q" needs to be relabeled to r, checking via the chain decompositions of D in the color of m:
        
        # Find first occurrence of m in hue chain decomposition, if any. The corresponding number is "q".
        # Look back at the starting index of q's chain. If the corresponding element of the number_chain_decomposition
        # is < r, keep q and set its hue to r and skip it later on.
        number_chain_decomposition, hue_chain_decomposition, start_idx_of_chains =\
            D.chain_decomposition(c, return_start_idx_of_chains=True)
        try:
            q_idx = hue_chain_decomposition.index(m[1])
            q = (c, number_chain_decomposition[q_idx])
            # find the start of the chain containing q_idx
            s_idx = [i for i in start_idx_of_chains if i <= q_idx][-1] # should NEVER fail because this list is [0, ...]
            s = number_chain_decomposition[s_idx]
            if s < r[1]:
                new_dec[q] = r
                r_mult -= 1
                skips.append(q)

        except ValueError:
            pass

        # Step 4: Relabel all remaining occurrences in the decoration as either m or r
        #         such that all r's precede all m's in "permission list order", uniquely 
        #         so as to protect the multiplicity.
        # Permission list order: first follow the number chain within the color c,
        # then follow everything else in numerical order.

        for ii in number_chain_decomposition:
            if (c, ii) in skips or D.dec[c, ii] != m:
                continue
            skips.append((c, ii))
            if r_mult > 0:
                new_dec[c, ii] = r
                r_mult -= 1
            else:
                new_dec[c, ii] = m
                m_mult -= 1 # unnecessary, just a sanity check

        for cc in range(D.num_colors):
            for ii in range(D.color_counts[cc]):
                if (cc, ii) in skips: # skip entries already covered in steps 1,2,3 and the number chain order portion
                    continue
                if D.dec[cc, ii] == m:
                    # try to make it r, unless all r's have been done, in which case make it m
                    if r_mult > 0:
                        new_dec[cc, ii] = r
                        r_mult -= 1
                    else:
                        new_dec[cc, ii] = m
                        m_mult -= 1 # unnecessary, just a sanity check
        
        # this better be true!
        assert m_mult == 0
        assert r_mult == 0
        
    if t < m:
        # t wins (merge case), necessarily t is not infinity
        # merge t into the block of r

        # NO EXCEPTIONS SHOULD EVER HAPPEN HERE

        # correct the new list of hues
        i = D.mins_of_hues[t[0]].index(r[1]) # find old block whose min is r
        old_block = new_hues[t[0]].pop(i) # delete it
        new_block = [t[1]] + old_block # insert t (new minimal element)
        i = new_hues[t[0]].index([t[1]]) # find where the singleton block [t] was
        new_hues[t[0]][t[1]] = new_block # replace the singleton with the new block

        # form the new decoration
        # things pointing at the old block should now point at t
        new_dec = {key:(t if D.dec[key] == r else D.dec[key]) for key in D.dec}

    return MismatchedDecoration(D.color_counts, D.exponents, new_hues, new_dec,
                                print_mode=D.print_mode, index_print_mode=D.index_print_mode)

# abbreviation
h = hue_involution

def all_mismatched_decorations(color_counts, exponents, print_mode="ordered", index_print_mode=1):
    """Generates all mismatched decorations for the given parameters."""

    # First we need to list all choices of hue partition in each color,
    # then we need to try all possible decorations.
    # For the decorations, we should first put in the forced (underlined boxed) entries.
    # We can also slightly improve efficiency by checking the Hall's inequalities.

    # Validate color_counts is a list of ints
    if not (isinstance(color_counts, list) and len(color_counts) >= 3 and
            all((isinstance(x, int) and x > 0) for x in color_counts)):
        raise TypeError("color_counts must be a list of at least 3 positive ints")
    
    total_points = sum(color_counts)
    
    # Validate exponents is a list of lists of ints
    if not (isinstance(exponents, list) and 
            all(isinstance(sublist, list) and all((isinstance(k, int) and k > 0) for k in sublist) for sublist in exponents)):
        raise TypeError("exponents must be a list of lists of positive ints")
        
    num_nonzero_exps_by_color = [len(exps_by_color) for exps_by_color in exponents]
    total_exps_by_color = [sum(exps_by_color) for exps_by_color in exponents]
    total_exp = sum(total_exps_by_color)
    
    if not(total_exp + 3 == total_points):
        raise ValueError("exponents must add up to number of points minus 3")
    
    # iterator yielding all possible hue partitions
    for hue_partitions in product(*(set_partitions(range(ell)) for ell in num_nonzero_exps_by_color)):
        # convert it to a list
        hue_partitions = list(hue_partitions)

        # now formulate all possible decorations.

        # all non-minimal entries of hue block are now forced.
        dec = {(c, i):(c, hue[0])
               for c, hue_partition in enumerate(hue_partitions)
               for hue in hue_partition
               for i in hue[1:]}
        
        # also, the three crossed out entries are forced.
        dec.update({(c, 0):(None, None) for c in [0, 1, 2]})
        
        leftover_exponents_by_hues = [[sum(exps_by_color[i] for i in part) - len(part) + 1 for part in hue_partition]
                                      for (hue_partition, exps_by_color) in zip(hue_partitions, exponents)]
        
        leftover_exponents_by_colors = [sum(sublist) for sublist in leftover_exponents_by_hues]
        unboxed_numbers = [[(c, i) for i in range(LH, LC) if not (c < 3 and i == 0)]
                           for c, (LC, LH) in enumerate(zip(color_counts, num_nonzero_exps_by_color))]
        
        # form the list of representatives of mins of hues, for use later
        mins_of_hues = [[(c, hue[0]) for hue in hue_partition] for c, hue_partition in enumerate(hue_partitions)]
        # exclude any crossed out entries when building the rest of the decoration
        leftover_boxed_numbers = [[m for m in ms if not (m[0] < 3 and m[1] == 0)] for ms in mins_of_hues]
        
        # form mismatched color assignments by tree search
        for mismatched_coloring in _helper_mismatched_colorings(leftover_exponents_by_colors, unboxed_numbers, leftover_boxed_numbers):

            # mismatched_coloring is a dict with key:value pairs (c, i): c' where c' is only a color.
            # Each color occurs the correct total number of times.
            # Thus, within each color, using leftover_exponents_by_hues, there is a multinomial coefficient
            # of choices to specialize those colors to hues. This is listed efficiently.
            for hue_choices in product(*(multinomial_assignment([p for p in mismatched_coloring if mismatched_coloring[p] == c], ms, es)
                                        for c, (es, ms) in enumerate(zip(leftover_exponents_by_hues, mins_of_hues)))):
                yield MismatchedDecoration(color_counts, exponents, hue_partitions,
                                           dec | {k: v for d in hue_choices for k, v in d.items()},
                                           print_mode, index_print_mode)

def _helper_mismatched_colorings(exponents, unboxed, leftover_boxed):
    """Helper function. Generates all matchings from (unboxed union leftover_boxed) to colors, such that unboxed are mismatched.
    It is assumed that the crossed out entries have already been excluded here. (This is OK because the values will just be colors,
    so we don't need to know if a crossed out entry represents a potential hue.)
    """

    n = sum(exponents)
    assert n == sum(len(us)+len(bs) for us, bs in zip(unboxed, leftover_boxed)) # sanity check: total exponent = total # entries
    hall_ineqs = [(c, n - len(u) - e) for c, (u, e) in enumerate(zip(unboxed, exponents)) if e != 0]
    
    # if hall inequalities are not satisfied, there are no mismatched colorings.
    if not all(ineq >= 0 for _, ineq in hall_ineqs):
        return
    
    if n == 0:
        # boundary case: no exponents left, no points left. note that there are no hall inequalities either.
        return dict()

    # an extreme case: if some len(u) + e == n, this means the exponent on color j is so high 
    # that everything available (unboxed non-color j, plus all boxed entries) must be assigned color j.
    # note: necessarily there is a boxed entry in row c_forced.
    try:
        c_forced = [c for c, ineq in hall_ineqs if ineq == 0][0]
        dec = dict()

        # everything that can be assigned color c_forced must be:
        for c, (us, bs) in enumerate(zip(unboxed, leftover_boxed)):
            # assign the boxed entries the color c_forced
            dec.update({b:c_forced for b in bs})
            if c != c_forced:
                # assign the unboxed entries the color c_forced
                dec.update({u:c_forced for u in us})
        
        # all that's left are the unboxed entries in color c_forced. these can be assigned freely!
        # also, since there was a boxed entry in color c_forced, the unboxed entries are not crossed out.
        other_colors, other_exponents = zip(*((c, e) for (c, e) in enumerate(exponents) if c != c_forced))
        for partial_dict in multinomial_assignment(unboxed[c_forced], other_colors, other_exponents):
            yield dec | partial_dict

        # there are now no more to find.
        return
    except IndexError:
        pass

    # otherwise, all inequalities are strict. choose a first assignment arbitrarily, then continue.
    # note: exponents can't all be 0! therefore the points can't all be zero either.
    
    # if all unboxed entries have been assigned, assign first remaining boxed point
    if all(len(us) == 0 for us in unboxed):

        c_b, i_b = [bs[0] for bs in leftover_boxed if len(bs) > 0][0] # should not cause an IndexError!
        
        # choose a color for it
        for c in range(len(exponents)):
            if exponents[c] == 0: continue

            # prepare data for recursive call
            es_rest = [e for e in exponents]
            es_rest[c] -= 1
            unboxed_rest = [[u for u in us] for us in unboxed]
            boxed_rest = [[b for b in bs] for bs in leftover_boxed]
            boxed_rest[c_b] = boxed_rest[c_b][1:] # remove the chosen element
            
            for result_rest in _helper_mismatched_colorings(es_rest, unboxed_rest, boxed_rest):
                yield {(c_b, i_b):c} | result_rest
    else:

        # choose first available unboxed point
        c_u, i_u = [us[0] for us in unboxed if len(us) > 0][0] # should not cause an IndexError!

        # choose a mismatching color for it
        for c in range(len(exponents)):
            if exponents[c] == 0 or c == c_u: continue

            # prepare data for recursive call
            es_rest = [e for e in exponents]
            es_rest[c] -= 1
            unboxed_rest = [[u for u in us] for us in unboxed]
            unboxed_rest[c_u] = unboxed_rest[c_u][1:] # remove the chosen element
            boxed_rest = [[b for b in bs] for bs in leftover_boxed]

            for result_rest in _helper_mismatched_colorings(es_rest, unboxed_rest, boxed_rest):
                yield {(c_u, i_u):c} | result_rest
