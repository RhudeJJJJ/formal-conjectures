/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0931 : Family 10 := level10.get ⟨1536,by decide⟩
def sourceMap0931 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0931 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0931_checked : acceptsGraphIso
    (source (graph core0931) (root 10) 0 0) DegreeTwoThreeSpectrum1297.graph sourceMap0931=true := by decide +kernel
theorem fusedMap0931_checked : acceptsGraphIso
    (fused (graph core0931) (root 10) 0 0) DegreeOneSmallSpectrum1543.graph fusedMap0931=true := by decide +kernel
theorem certified0931 : Certified (graph core0931) (root 10) 0 0 :=
  of_native_maps core0931 DegreeTwoThreeSpectrum1297.graph DegreeOneSmallSpectrum1543.graph
    sourceMap0931 fusedMap0931 sourceMap0931_checked fusedMap0931_checked
    DegreeTwoThreeFiniteComparisons.comparison0931
#print axioms sourceMap0931_checked
#print axioms fusedMap0931_checked
#print axioms certified0931
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
