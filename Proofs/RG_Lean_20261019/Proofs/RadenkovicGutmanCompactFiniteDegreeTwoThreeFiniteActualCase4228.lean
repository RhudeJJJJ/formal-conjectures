/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4228 : Family 9 := level9.get ⟨146,by decide⟩
def sourceMap4228 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4228 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4228_checked : acceptsGraphIso
    (source (graph core4228) (root 9) 2 2) DegreeTwoThreeSpectrum4707.graph sourceMap4228=true := by decide +kernel
theorem fusedMap4228_checked : acceptsGraphIso
    (fused (graph core4228) (root 9) 2 2) DegreeTwoThreeSpectrum3901.graph fusedMap4228=true := by decide +kernel
theorem certified4228 : Certified (graph core4228) (root 9) 2 2 :=
  of_native_maps core4228 DegreeTwoThreeSpectrum4707.graph DegreeTwoThreeSpectrum3901.graph
    sourceMap4228 fusedMap4228 sourceMap4228_checked fusedMap4228_checked
    DegreeTwoThreeFiniteComparisons.comparison4228
#print axioms sourceMap4228_checked
#print axioms fusedMap4228_checked
#print axioms certified4228
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
