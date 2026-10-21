/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0990 : Family 8 := level8.get ⟨96,by decide⟩
def sourceMap0990 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0990 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0990_checked : acceptsGraphIso
    (source (graph core0990) (root 8) 1 1) DegreeOneSmallSpectrum1582.graph sourceMap0990=true := by decide +kernel
theorem fusedMap0990_checked : acceptsGraphIso
    (fused (graph core0990) (root 8) 1 1) DegreeOneSmallSpectrum992.graph fusedMap0990=true := by decide +kernel
theorem certified0990 : Certified (graph core0990) (root 8) 1 1 :=
  of_native_maps core0990 DegreeOneSmallSpectrum1582.graph DegreeOneSmallSpectrum992.graph
    sourceMap0990 fusedMap0990 sourceMap0990_checked fusedMap0990_checked
    DegreeOneSmallComparisons.comparison0990
#print axioms sourceMap0990_checked
#print axioms fusedMap0990_checked
#print axioms certified0990
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
