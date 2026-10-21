/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0878 : Family 8 := level8.get ⟨45,by decide⟩
def sourceMap0878 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0878 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0878_checked : acceptsGraphIso
    (source (graph core0878) (root 8) 1 1) DegreeOneSmallSpectrum1219.graph sourceMap0878=true := by decide +kernel
theorem fusedMap0878_checked : acceptsGraphIso
    (fused (graph core0878) (root 8) 1 1) DegreeOneSmallSpectrum881.graph fusedMap0878=true := by decide +kernel
theorem certified0878 : Certified (graph core0878) (root 8) 1 1 :=
  of_native_maps core0878 DegreeOneSmallSpectrum1219.graph DegreeOneSmallSpectrum881.graph
    sourceMap0878 fusedMap0878 sourceMap0878_checked fusedMap0878_checked
    DegreeOneSmallComparisons.comparison0878
#print axioms sourceMap0878_checked
#print axioms fusedMap0878_checked
#print axioms certified0878
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
