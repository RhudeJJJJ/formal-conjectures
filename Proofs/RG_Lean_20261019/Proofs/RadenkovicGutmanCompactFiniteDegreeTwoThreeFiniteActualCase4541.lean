/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4541 : Family 10 := level10.get ⟨422,by decide⟩
def sourceMap4541 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,10,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4541 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4541_checked : acceptsGraphIso
    (source (graph core4541) (root 10) 2 2) DegreeTwoThreeSpectrum6806.graph sourceMap4541=true := by decide +kernel
theorem fusedMap4541_checked : acceptsGraphIso
    (fused (graph core4541) (root 10) 2 2) DegreeTwoThreeSpectrum5809.graph fusedMap4541=true := by decide +kernel
theorem certified4541 : Certified (graph core4541) (root 10) 2 2 :=
  of_native_maps core4541 DegreeTwoThreeSpectrum6806.graph DegreeTwoThreeSpectrum5809.graph
    sourceMap4541 fusedMap4541 sourceMap4541_checked fusedMap4541_checked
    DegreeTwoThreeFiniteComparisons.comparison4541
#print axioms sourceMap4541_checked
#print axioms fusedMap4541_checked
#print axioms certified4541
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
