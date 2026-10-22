/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4929 : Family 10 := level10.get ⟨1439,by decide⟩
def sourceMap4929 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,9,10,11,12,13,14,15,16,7,8,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4929 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4929_checked : acceptsGraphIso
    (source (graph core4929) (root 10) 2 2) DegreeTwoThreeSpectrum7505.graph sourceMap4929=true := by decide +kernel
theorem fusedMap4929_checked : acceptsGraphIso
    (fused (graph core4929) (root 10) 2 2) DegreeTwoThreeSpectrum6899.graph fusedMap4929=true := by decide +kernel
theorem certified4929 : Certified (graph core4929) (root 10) 2 2 :=
  of_native_maps core4929 DegreeTwoThreeSpectrum7505.graph DegreeTwoThreeSpectrum6899.graph
    sourceMap4929 fusedMap4929 sourceMap4929_checked fusedMap4929_checked
    DegreeTwoThreeFiniteComparisons.comparison4929
#print axioms sourceMap4929_checked
#print axioms fusedMap4929_checked
#print axioms certified4929
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
