/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0870 : Family 8 := level8.get ⟨42,by decide⟩
def sourceMap0870 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 8 1 1 v)
def fusedMap0870 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0870_checked : acceptsGraphIso
    (source (graph core0870) (root 8) 1 1) DegreeOneSmallSpectrum1165.graph sourceMap0870=true := by decide +kernel
theorem fusedMap0870_checked : acceptsGraphIso
    (fused (graph core0870) (root 8) 1 1) DegreeOneSmallSpectrum874.graph fusedMap0870=true := by decide +kernel
theorem certified0870 : Certified (graph core0870) (root 8) 1 1 :=
  of_native_maps core0870 DegreeOneSmallSpectrum1165.graph DegreeOneSmallSpectrum874.graph
    sourceMap0870 fusedMap0870 sourceMap0870_checked fusedMap0870_checked
    DegreeOneSmallComparisons.comparison0870
#print axioms sourceMap0870_checked
#print axioms fusedMap0870_checked
#print axioms certified0870
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
