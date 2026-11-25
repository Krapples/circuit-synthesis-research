"""Truth-table operations in the original private-variable coordinates."""

from module_contraction import vars as truth_variables


class PackedTables:
    def __init__(self, variables):
        self.full = (1 << variables) - 1
        self.one = (1 << (1 << variables)) - 1
        self.columns = truth_variables(variables)
        self.low_columns = tuple(self.one ^ column for column in self.columns)

    def support(self, table):
        """Compare the two halves for each coordinate in parallel."""
        if table in (0, self.one):
            return 0
        return sum(1 << i for i, low in enumerate(self.low_columns) if (table ^ (table >> (1 << i))) & low)

    def project(self, table, inside, exists):
        """Quantify outside coordinates and repeat the result at their assignments."""
        outside = self.full ^ inside
        while outside:
            shift = outside & -outside
            outside ^= shift
            axis = shift.bit_length() - 1
            swapped = ((table & self.low_columns[axis]) << shift) | ((table & self.columns[axis]) >> shift)
            table = table | swapped if exists else table & swapped
        return table

    def exposed(self, table, inside, project=None):
        """Return the common nonconstant cofactor, if one exists."""
        if not inside or table in (0, self.one):
            return None
        if inside == self.full:
            return table
        if project is None:
            project = self.project
        outside = self.full ^ inside
        active = project(table, outside, True) & ~project(table, outside, False)
        if not active:
            return None
        candidate = project(table & active, inside, True)
        return candidate if not (table ^ candidate) & active else None
