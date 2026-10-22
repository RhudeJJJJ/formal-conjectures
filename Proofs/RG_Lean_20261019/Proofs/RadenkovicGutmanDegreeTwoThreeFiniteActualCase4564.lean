/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4564 : Family 10 := level10.get ⟨485,by decide⟩
def sourceMap4564 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,11,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4564 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 2 2 v)
theorem sourceMap4564_checked : acceptsGraphIso
    (source (graph core4564) (root 10) 2 2) DegreeTwoThreeSpectrum6800.graph sourceMap4564=true := by decide +kernel
theorem fusedMap4564_checked : acceptsGraphIso
    (fused (graph core4564) (root 10) 2 2) DegreeTwoThreeSpectrum5951.graph fusedMap4564=true := by decide +kernel
theorem certified4564 : Certified (graph core4564) (root 10) 2 2 :=
  of_native_maps core4564 DegreeTwoThreeSpectrum6800.graph DegreeTwoThreeSpectrum5951.graph
    sourceMap4564 fusedMap4564 sourceMap4564_checked fusedMap4564_checked
    DegreeTwoThreeFiniteComparisons.comparison4564
#print axioms sourceMap4564_checked
#print axioms fusedMap4564_checked
#print axioms certified4564
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
