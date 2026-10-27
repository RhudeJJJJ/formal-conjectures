/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4271 : Family 9 := level9.get ⟨278,by decide⟩
def sourceMap4271 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4271 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4271_checked : acceptsGraphIso
    (source (graph core4271) (root 9) 2 2) DegreeTwoThreeSpectrum4894.graph sourceMap4271=true := by decide +kernel
theorem fusedMap4271_checked : acceptsGraphIso
    (fused (graph core4271) (root 9) 2 2) DegreeTwoThreeSpectrum4095.graph fusedMap4271=true := by decide +kernel
theorem certified4271 : Certified (graph core4271) (root 9) 2 2 :=
  of_native_maps core4271 DegreeTwoThreeSpectrum4894.graph DegreeTwoThreeSpectrum4095.graph
    sourceMap4271 fusedMap4271 sourceMap4271_checked fusedMap4271_checked
    DegreeTwoThreeFiniteComparisons.comparison4271
#print axioms sourceMap4271_checked
#print axioms fusedMap4271_checked
#print axioms certified4271
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
