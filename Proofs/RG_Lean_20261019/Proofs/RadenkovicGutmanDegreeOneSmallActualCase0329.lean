/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0329 : Family 6 := level6.get ⟨7,by decide⟩
def sourceMap0329 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap0329 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0329_checked : acceptsGraphIso
    (source (graph core0329) (root 6) 2 2) DegreeOneSmallSpectrum1174.graph sourceMap0329=true := by decide +kernel
theorem fusedMap0329_checked : acceptsGraphIso
    (fused (graph core0329) (root 6) 2 2) DegreeOneSmallSpectrum879.graph fusedMap0329=true := by decide +kernel
theorem certified0329 : Certified (graph core0329) (root 6) 2 2 :=
  of_native_maps core0329 DegreeOneSmallSpectrum1174.graph DegreeOneSmallSpectrum879.graph
    sourceMap0329 fusedMap0329 sourceMap0329_checked fusedMap0329_checked
    DegreeOneSmallComparisons.comparison0329
#print axioms sourceMap0329_checked
#print axioms fusedMap0329_checked
#print axioms certified0329
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
