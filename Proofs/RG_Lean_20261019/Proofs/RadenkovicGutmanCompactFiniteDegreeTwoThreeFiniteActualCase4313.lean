/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4313 : Family 9 := level9.get ⟨389,by decide⟩
def sourceMap4313 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4313 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4313_checked : acceptsGraphIso
    (source (graph core4313) (root 9) 2 2) DegreeTwoThreeSpectrum4767.graph sourceMap4313=true := by decide +kernel
theorem fusedMap4313_checked : acceptsGraphIso
    (fused (graph core4313) (root 9) 2 2) DegreeTwoThreeSpectrum4338.graph fusedMap4313=true := by decide +kernel
theorem certified4313 : Certified (graph core4313) (root 9) 2 2 :=
  of_native_maps core4313 DegreeTwoThreeSpectrum4767.graph DegreeTwoThreeSpectrum4338.graph
    sourceMap4313 fusedMap4313 sourceMap4313_checked fusedMap4313_checked
    DegreeTwoThreeFiniteComparisons.comparison4313
#print axioms sourceMap4313_checked
#print axioms fusedMap4313_checked
#print axioms certified4313
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
