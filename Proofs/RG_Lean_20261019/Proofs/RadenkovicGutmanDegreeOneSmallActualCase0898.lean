/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0898 : Family 8 := level8.get ⟨54,by decide⟩
def sourceMap0898 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0898 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0898_checked : acceptsGraphIso
    (source (graph core0898) (root 8) 1 1) DegreeOneSmallSpectrum1324.graph sourceMap0898=true := by decide +kernel
theorem fusedMap0898_checked : acceptsGraphIso
    (fused (graph core0898) (root 8) 1 1) DegreeOneSmallSpectrum910.graph fusedMap0898=true := by decide +kernel
theorem certified0898 : Certified (graph core0898) (root 8) 1 1 :=
  of_native_maps core0898 DegreeOneSmallSpectrum1324.graph DegreeOneSmallSpectrum910.graph
    sourceMap0898 fusedMap0898 sourceMap0898_checked fusedMap0898_checked
    DegreeOneSmallComparisons.comparison0898
#print axioms sourceMap0898_checked
#print axioms fusedMap0898_checked
#print axioms certified0898
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
