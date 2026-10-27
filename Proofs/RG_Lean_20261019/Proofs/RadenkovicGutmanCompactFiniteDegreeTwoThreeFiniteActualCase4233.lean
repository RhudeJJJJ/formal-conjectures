/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4233 : Family 9 := level9.get ⟨164,by decide⟩
def sourceMap4233 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4233 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4233_checked : acceptsGraphIso
    (source (graph core4233) (root 9) 2 2) DegreeTwoThreeSpectrum4743.graph sourceMap4233=true := by decide +kernel
theorem fusedMap4233_checked : acceptsGraphIso
    (fused (graph core4233) (root 9) 2 2) DegreeTwoThreeSpectrum3925.graph fusedMap4233=true := by decide +kernel
theorem certified4233 : Certified (graph core4233) (root 9) 2 2 :=
  of_native_maps core4233 DegreeTwoThreeSpectrum4743.graph DegreeTwoThreeSpectrum3925.graph
    sourceMap4233 fusedMap4233 sourceMap4233_checked fusedMap4233_checked
    DegreeTwoThreeFiniteComparisons.comparison4233
#print axioms sourceMap4233_checked
#print axioms fusedMap4233_checked
#print axioms certified4233
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
