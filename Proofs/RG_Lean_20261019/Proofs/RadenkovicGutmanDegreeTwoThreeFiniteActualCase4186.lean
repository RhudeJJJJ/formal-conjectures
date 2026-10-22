/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4186 : Family 8 := level8.get ⟨248,by decide⟩
def sourceMap4186 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap4186 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4186_checked : acceptsGraphIso
    (source (graph core4186) (root 8) 2 2) DegreeTwoThreeSpectrum3846.graph sourceMap4186=true := by decide +kernel
theorem fusedMap4186_checked : acceptsGraphIso
    (fused (graph core4186) (root 8) 2 2) DegreeTwoThreeSpectrum2731.graph fusedMap4186=true := by decide +kernel
theorem certified4186 : Certified (graph core4186) (root 8) 2 2 :=
  of_native_maps core4186 DegreeTwoThreeSpectrum3846.graph DegreeTwoThreeSpectrum2731.graph
    sourceMap4186 fusedMap4186 sourceMap4186_checked fusedMap4186_checked
    DegreeTwoThreeFiniteComparisons.comparison4186
#print axioms sourceMap4186_checked
#print axioms fusedMap4186_checked
#print axioms certified4186
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
