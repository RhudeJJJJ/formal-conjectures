/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4240 : Family 9 := level9.get ⟨185,by decide⟩
def sourceMap4240 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4240 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4240_checked : acceptsGraphIso
    (source (graph core4240) (root 9) 2 2) DegreeTwoThreeSpectrum4779.graph sourceMap4240=true := by decide +kernel
theorem fusedMap4240_checked : acceptsGraphIso
    (fused (graph core4240) (root 9) 2 2) DegreeTwoThreeSpectrum3954.graph fusedMap4240=true := by decide +kernel
theorem certified4240 : Certified (graph core4240) (root 9) 2 2 :=
  of_native_maps core4240 DegreeTwoThreeSpectrum4779.graph DegreeTwoThreeSpectrum3954.graph
    sourceMap4240 fusedMap4240 sourceMap4240_checked fusedMap4240_checked
    DegreeTwoThreeFiniteComparisons.comparison4240
#print axioms sourceMap4240_checked
#print axioms fusedMap4240_checked
#print axioms certified4240
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
