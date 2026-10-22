/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4220 : Family 9 := level9.get ⟨122,by decide⟩
def sourceMap4220 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,9,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4220 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4220_checked : acceptsGraphIso
    (source (graph core4220) (root 9) 2 2) DegreeTwoThreeSpectrum4548.graph sourceMap4220=true := by decide +kernel
theorem fusedMap4220_checked : acceptsGraphIso
    (fused (graph core4220) (root 9) 2 2) DegreeTwoThreeSpectrum4145.graph fusedMap4220=true := by decide +kernel
theorem certified4220 : Certified (graph core4220) (root 9) 2 2 :=
  of_native_maps core4220 DegreeTwoThreeSpectrum4548.graph DegreeTwoThreeSpectrum4145.graph
    sourceMap4220 fusedMap4220 sourceMap4220_checked fusedMap4220_checked
    DegreeTwoThreeFiniteComparisons.comparison4220
#print axioms sourceMap4220_checked
#print axioms fusedMap4220_checked
#print axioms certified4220
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
