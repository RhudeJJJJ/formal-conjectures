/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4241 : Family 9 := level9.get ⟨190,by decide⟩
def sourceMap4241 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,14,15,13,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4241 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4241_checked : acceptsGraphIso
    (source (graph core4241) (root 9) 2 2) DegreeTwoThreeSpectrum4786.graph sourceMap4241=true := by decide +kernel
theorem fusedMap4241_checked : acceptsGraphIso
    (fused (graph core4241) (root 9) 2 2) DegreeTwoThreeSpectrum3962.graph fusedMap4241=true := by decide +kernel
theorem certified4241 : Certified (graph core4241) (root 9) 2 2 :=
  of_native_maps core4241 DegreeTwoThreeSpectrum4786.graph DegreeTwoThreeSpectrum3962.graph
    sourceMap4241 fusedMap4241 sourceMap4241_checked fusedMap4241_checked
    DegreeTwoThreeFiniteComparisons.comparison4241
#print axioms sourceMap4241_checked
#print axioms fusedMap4241_checked
#print axioms certified4241
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
