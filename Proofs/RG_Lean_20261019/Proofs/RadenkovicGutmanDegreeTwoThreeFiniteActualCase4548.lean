/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4548 : Family 10 := level10.get ⟨445,by decide⟩
def sourceMap4548 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4548 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4548_checked : acceptsGraphIso
    (source (graph core4548) (root 10) 2 2) DegreeTwoThreeSpectrum6813.graph sourceMap4548=true := by decide +kernel
theorem fusedMap4548_checked : acceptsGraphIso
    (fused (graph core4548) (root 10) 2 2) DegreeTwoThreeSpectrum5866.graph fusedMap4548=true := by decide +kernel
theorem certified4548 : Certified (graph core4548) (root 10) 2 2 :=
  of_native_maps core4548 DegreeTwoThreeSpectrum6813.graph DegreeTwoThreeSpectrum5866.graph
    sourceMap4548 fusedMap4548 sourceMap4548_checked fusedMap4548_checked
    DegreeTwoThreeFiniteComparisons.comparison4548
#print axioms sourceMap4548_checked
#print axioms fusedMap4548_checked
#print axioms certified4548
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
