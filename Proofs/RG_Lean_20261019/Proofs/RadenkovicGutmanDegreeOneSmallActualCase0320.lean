/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0320 : Family 6 := level6.get ⟨6,by decide⟩
def sourceMap0320 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap0320 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0320_checked : acceptsGraphIso
    (source (graph core0320) (root 6) 2 2) DegreeOneSmallSpectrum1074.graph sourceMap0320=true := by decide +kernel
theorem fusedMap0320_checked : acceptsGraphIso
    (fused (graph core0320) (root 6) 2 2) DegreeOneSmallSpectrum870.graph fusedMap0320=true := by decide +kernel
theorem certified0320 : Certified (graph core0320) (root 6) 2 2 :=
  of_native_maps core0320 DegreeOneSmallSpectrum1074.graph DegreeOneSmallSpectrum870.graph
    sourceMap0320 fusedMap0320 sourceMap0320_checked fusedMap0320_checked
    DegreeOneSmallComparisons.comparison0320
#print axioms sourceMap0320_checked
#print axioms fusedMap0320_checked
#print axioms certified0320
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
