/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0878 : Family 10 := level10.get ⟨1391,by decide⟩
def sourceMap0878 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0878 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0878_checked : acceptsGraphIso
    (source (graph core0878) (root 10) 0 0) DegreeOneSmallSpectrum1145.graph sourceMap0878=true := by decide +kernel
theorem fusedMap0878_checked : acceptsGraphIso
    (fused (graph core0878) (root 10) 0 0) DegreeOneSmallSpectrum1140.graph fusedMap0878=true := by decide +kernel
theorem certified0878 : Certified (graph core0878) (root 10) 0 0 :=
  of_native_maps core0878 DegreeOneSmallSpectrum1145.graph DegreeOneSmallSpectrum1140.graph
    sourceMap0878 fusedMap0878 sourceMap0878_checked fusedMap0878_checked
    DegreeTwoThreeFiniteComparisons.comparison0878
#print axioms sourceMap0878_checked
#print axioms fusedMap0878_checked
#print axioms certified0878
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
