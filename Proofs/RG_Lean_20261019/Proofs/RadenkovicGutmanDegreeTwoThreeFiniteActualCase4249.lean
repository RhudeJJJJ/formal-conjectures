/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4249 : Family 9 := level9.get ⟨211,by decide⟩
def sourceMap4249 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4249 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4249_checked : acceptsGraphIso
    (source (graph core4249) (root 9) 2 2) DegreeTwoThreeSpectrum4812.graph sourceMap4249=true := by decide +kernel
theorem fusedMap4249_checked : acceptsGraphIso
    (fused (graph core4249) (root 9) 2 2) DegreeTwoThreeSpectrum3996.graph fusedMap4249=true := by decide +kernel
theorem certified4249 : Certified (graph core4249) (root 9) 2 2 :=
  of_native_maps core4249 DegreeTwoThreeSpectrum4812.graph DegreeTwoThreeSpectrum3996.graph
    sourceMap4249 fusedMap4249 sourceMap4249_checked fusedMap4249_checked
    DegreeTwoThreeFiniteComparisons.comparison4249
#print axioms sourceMap4249_checked
#print axioms fusedMap4249_checked
#print axioms certified4249
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
