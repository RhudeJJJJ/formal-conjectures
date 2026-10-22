/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4338 : Family 9 := level9.get ⟨451,by decide⟩
def sourceMap4338 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4338 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4338_checked : acceptsGraphIso
    (source (graph core4338) (root 9) 2 2) DegreeTwoThreeSpectrum4829.graph sourceMap4338=true := by decide +kernel
theorem fusedMap4338_checked : acceptsGraphIso
    (fused (graph core4338) (root 9) 2 2) DegreeTwoThreeSpectrum4467.graph fusedMap4338=true := by decide +kernel
theorem certified4338 : Certified (graph core4338) (root 9) 2 2 :=
  of_native_maps core4338 DegreeTwoThreeSpectrum4829.graph DegreeTwoThreeSpectrum4467.graph
    sourceMap4338 fusedMap4338 sourceMap4338_checked fusedMap4338_checked
    DegreeTwoThreeFiniteComparisons.comparison4338
#print axioms sourceMap4338_checked
#print axioms fusedMap4338_checked
#print axioms certified4338
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
