/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4278 : Family 9 := level9.get ⟨297,by decide⟩
def sourceMap4278 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4278 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4278_checked : acceptsGraphIso
    (source (graph core4278) (root 9) 2 2) DegreeTwoThreeSpectrum4898.graph sourceMap4278=true := by decide +kernel
theorem fusedMap4278_checked : acceptsGraphIso
    (fused (graph core4278) (root 9) 2 2) DegreeTwoThreeSpectrum4126.graph fusedMap4278=true := by decide +kernel
theorem certified4278 : Certified (graph core4278) (root 9) 2 2 :=
  of_native_maps core4278 DegreeTwoThreeSpectrum4898.graph DegreeTwoThreeSpectrum4126.graph
    sourceMap4278 fusedMap4278 sourceMap4278_checked fusedMap4278_checked
    DegreeTwoThreeFiniteComparisons.comparison4278
#print axioms sourceMap4278_checked
#print axioms fusedMap4278_checked
#print axioms certified4278
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
