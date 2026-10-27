/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4206 : Family 9 := level9.get ⟨67,by decide⟩
def sourceMap4206 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4206 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 2 2 v)
theorem sourceMap4206_checked : acceptsGraphIso
    (source (graph core4206) (root 9) 2 2) DegreeTwoThreeSpectrum4385.graph sourceMap4206=true := by decide +kernel
theorem fusedMap4206_checked : acceptsGraphIso
    (fused (graph core4206) (root 9) 2 2) DegreeTwoThreeSpectrum3980.graph fusedMap4206=true := by decide +kernel
theorem certified4206 : Certified (graph core4206) (root 9) 2 2 :=
  of_native_maps core4206 DegreeTwoThreeSpectrum4385.graph DegreeTwoThreeSpectrum3980.graph
    sourceMap4206 fusedMap4206 sourceMap4206_checked fusedMap4206_checked
    DegreeTwoThreeFiniteComparisons.comparison4206
#print axioms sourceMap4206_checked
#print axioms fusedMap4206_checked
#print axioms certified4206
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
