/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4376 : Family 9 := level9.get ⟨535,by decide⟩
def sourceMap4376 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,12,13,14,15,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4376 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4376_checked : acceptsGraphIso
    (source (graph core4376) (root 9) 2 2) DegreeTwoThreeSpectrum4866.graph sourceMap4376=true := by decide +kernel
theorem fusedMap4376_checked : acceptsGraphIso
    (fused (graph core4376) (root 9) 2 2) DegreeTwoThreeSpectrum4645.graph fusedMap4376=true := by decide +kernel
theorem certified4376 : Certified (graph core4376) (root 9) 2 2 :=
  of_native_maps core4376 DegreeTwoThreeSpectrum4866.graph DegreeTwoThreeSpectrum4645.graph
    sourceMap4376 fusedMap4376 sourceMap4376_checked fusedMap4376_checked
    DegreeTwoThreeFiniteComparisons.comparison4376
#print axioms sourceMap4376_checked
#print axioms fusedMap4376_checked
#print axioms certified4376
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
