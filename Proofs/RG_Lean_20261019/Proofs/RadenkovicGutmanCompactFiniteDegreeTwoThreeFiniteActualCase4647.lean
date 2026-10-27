/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4647 : Family 10 := level10.get ⟨735,by decide⟩
def sourceMap4647 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4647 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4647_checked : acceptsGraphIso
    (source (graph core4647) (root 10) 2 2) DegreeTwoThreeSpectrum7397.graph sourceMap4647=true := by decide +kernel
theorem fusedMap4647_checked : acceptsGraphIso
    (fused (graph core4647) (root 10) 2 2) DegreeTwoThreeSpectrum5492.graph fusedMap4647=true := by decide +kernel
theorem certified4647 : Certified (graph core4647) (root 10) 2 2 :=
  of_native_maps core4647 DegreeTwoThreeSpectrum7397.graph DegreeTwoThreeSpectrum5492.graph
    sourceMap4647 fusedMap4647 sourceMap4647_checked fusedMap4647_checked
    DegreeTwoThreeFiniteComparisons.comparison4647
#print axioms sourceMap4647_checked
#print axioms fusedMap4647_checked
#print axioms certified4647
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
