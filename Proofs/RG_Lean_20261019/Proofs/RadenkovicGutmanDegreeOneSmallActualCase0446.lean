/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0446 : Family 6 := level6.get ⟨37,by decide⟩
def sourceMap0446 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 6 2 2 v)
def fusedMap0446 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0446_checked : acceptsGraphIso
    (source (graph core0446) (root 6) 2 2) DegreeOneSmallSpectrum1976.graph sourceMap0446=true := by decide +kernel
theorem fusedMap0446_checked : acceptsGraphIso
    (fused (graph core0446) (root 6) 2 2) DegreeOneSmallSpectrum985.graph fusedMap0446=true := by decide +kernel
theorem certified0446 : Certified (graph core0446) (root 6) 2 2 :=
  of_native_maps core0446 DegreeOneSmallSpectrum1976.graph DegreeOneSmallSpectrum985.graph
    sourceMap0446 fusedMap0446 sourceMap0446_checked fusedMap0446_checked
    DegreeOneSmallComparisons.comparison0446
#print axioms sourceMap0446_checked
#print axioms fusedMap0446_checked
#print axioms certified0446
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
