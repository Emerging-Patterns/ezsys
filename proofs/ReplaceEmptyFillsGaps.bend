# proofs of laws/ReplaceEmptyFillsGaps.bend
import Base
import ../laws/ReplaceEmptyFillsGaps.bend as Laws
import ./lemmas/TextScan.bend as M1

def Laws.replace_gaps(_h, _t, _new):
  {==}

def Laws.replace_gaps_end(new):
  M1.app_nil(new)
