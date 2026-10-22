/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4231 : Family 9 := level9.get ⟨154,by decide⟩
def sourceMap4231 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4231 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4231_checked : acceptsGraphIso
    (source (graph core4231) (root 9) 2 2) DegreeTwoThreeSpectrum4720.graph sourceMap4231=true := by decide +kernel
theorem fusedMap4231_checked : acceptsGraphIso
    (fused (graph core4231) (root 9) 2 2) DegreeTwoThreeSpectrum3912.graph fusedMap4231=true := by decide +kernel
theorem certified4231 : Certified (graph core4231) (root 9) 2 2 :=
  of_native_maps core4231 DegreeTwoThreeSpectrum4720.graph DegreeTwoThreeSpectrum3912.graph
    sourceMap4231 fusedMap4231 sourceMap4231_checked fusedMap4231_checked
    DegreeTwoThreeFiniteComparisons.comparison4231
#print axioms sourceMap4231_checked
#print axioms fusedMap4231_checked
#print axioms certified4231
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
