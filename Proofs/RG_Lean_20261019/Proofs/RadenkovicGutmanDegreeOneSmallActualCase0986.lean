/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0986 : Family 8 := level8.get ⟨95,by decide⟩
def sourceMap0986 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0986 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0986_checked : acceptsGraphIso
    (source (graph core0986) (root 8) 1 1) DegreeOneSmallSpectrum1550.graph sourceMap0986=true := by decide +kernel
theorem fusedMap0986_checked : acceptsGraphIso
    (fused (graph core0986) (root 8) 1 1) DegreeOneSmallSpectrum985.graph fusedMap0986=true := by decide +kernel
theorem certified0986 : Certified (graph core0986) (root 8) 1 1 :=
  of_native_maps core0986 DegreeOneSmallSpectrum1550.graph DegreeOneSmallSpectrum985.graph
    sourceMap0986 fusedMap0986 sourceMap0986_checked fusedMap0986_checked
    DegreeOneSmallComparisons.comparison0986
#print axioms sourceMap0986_checked
#print axioms fusedMap0986_checked
#print axioms certified0986
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
