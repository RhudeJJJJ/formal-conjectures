/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4284 : Family 9 := level9.get ⟨308,by decide⟩
def sourceMap4284 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,11,12,13,14,15,1,2,3,4,5,6,7,8,9,10] (sourceLabel 9 2 2 v)
def fusedMap4284 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4284_checked : acceptsGraphIso
    (source (graph core4284) (root 9) 2 2) DegreeTwoThreeSpectrum4640.graph sourceMap4284=true := by decide +kernel
theorem fusedMap4284_checked : acceptsGraphIso
    (fused (graph core4284) (root 9) 2 2) DegreeTwoThreeSpectrum4150.graph fusedMap4284=true := by decide +kernel
theorem certified4284 : Certified (graph core4284) (root 9) 2 2 :=
  of_native_maps core4284 DegreeTwoThreeSpectrum4640.graph DegreeTwoThreeSpectrum4150.graph
    sourceMap4284 fusedMap4284 sourceMap4284_checked fusedMap4284_checked
    DegreeTwoThreeFiniteComparisons.comparison4284
#print axioms sourceMap4284_checked
#print axioms fusedMap4284_checked
#print axioms certified4284
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
