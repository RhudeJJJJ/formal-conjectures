/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4244 : Family 9 := level9.get ⟨195,by decide⟩
def sourceMap4244 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4244 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4244_checked : acceptsGraphIso
    (source (graph core4244) (root 9) 2 2) DegreeTwoThreeSpectrum4782.graph sourceMap4244=true := by decide +kernel
theorem fusedMap4244_checked : acceptsGraphIso
    (fused (graph core4244) (root 9) 2 2) DegreeTwoThreeSpectrum3971.graph fusedMap4244=true := by decide +kernel
theorem certified4244 : Certified (graph core4244) (root 9) 2 2 :=
  of_native_maps core4244 DegreeTwoThreeSpectrum4782.graph DegreeTwoThreeSpectrum3971.graph
    sourceMap4244 fusedMap4244 sourceMap4244_checked fusedMap4244_checked
    DegreeTwoThreeFiniteComparisons.comparison4244
#print axioms sourceMap4244_checked
#print axioms fusedMap4244_checked
#print axioms certified4244
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
