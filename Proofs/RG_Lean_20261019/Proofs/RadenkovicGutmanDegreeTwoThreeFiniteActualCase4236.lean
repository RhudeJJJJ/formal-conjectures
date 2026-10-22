/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4236 : Family 9 := level9.get ⟨172,by decide⟩
def sourceMap4236 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4236 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4236_checked : acceptsGraphIso
    (source (graph core4236) (root 9) 2 2) DegreeTwoThreeSpectrum4756.graph sourceMap4236=true := by decide +kernel
theorem fusedMap4236_checked : acceptsGraphIso
    (fused (graph core4236) (root 9) 2 2) DegreeTwoThreeSpectrum3936.graph fusedMap4236=true := by decide +kernel
theorem certified4236 : Certified (graph core4236) (root 9) 2 2 :=
  of_native_maps core4236 DegreeTwoThreeSpectrum4756.graph DegreeTwoThreeSpectrum3936.graph
    sourceMap4236 fusedMap4236 sourceMap4236_checked fusedMap4236_checked
    DegreeTwoThreeFiniteComparisons.comparison4236
#print axioms sourceMap4236_checked
#print axioms fusedMap4236_checked
#print axioms certified4236
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
