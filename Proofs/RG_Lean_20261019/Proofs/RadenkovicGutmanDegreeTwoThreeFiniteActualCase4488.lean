/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4488 : Family 10 := level10.get ⟨249,by decide⟩
def sourceMap4488 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4488 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4488_checked : acceptsGraphIso
    (source (graph core4488) (root 10) 2 2) DegreeTwoThreeSpectrum6396.graph sourceMap4488=true := by decide +kernel
theorem fusedMap4488_checked : acceptsGraphIso
    (fused (graph core4488) (root 10) 2 2) DegreeTwoThreeSpectrum5338.graph fusedMap4488=true := by decide +kernel
theorem certified4488 : Certified (graph core4488) (root 10) 2 2 :=
  of_native_maps core4488 DegreeTwoThreeSpectrum6396.graph DegreeTwoThreeSpectrum5338.graph
    sourceMap4488 fusedMap4488 sourceMap4488_checked fusedMap4488_checked
    DegreeTwoThreeFiniteComparisons.comparison4488
#print axioms sourceMap4488_checked
#print axioms fusedMap4488_checked
#print axioms certified4488
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
