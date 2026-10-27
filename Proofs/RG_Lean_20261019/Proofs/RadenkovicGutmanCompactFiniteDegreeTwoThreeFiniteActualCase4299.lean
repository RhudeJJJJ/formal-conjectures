/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4299 : Family 9 := level9.get ⟨350,by decide⟩
def sourceMap4299 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4299 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4299_checked : acceptsGraphIso
    (source (graph core4299) (root 9) 2 2) DegreeTwoThreeSpectrum4718.graph sourceMap4299=true := by decide +kernel
theorem fusedMap4299_checked : acceptsGraphIso
    (fused (graph core4299) (root 9) 2 2) DegreeTwoThreeSpectrum4251.graph fusedMap4299=true := by decide +kernel
theorem certified4299 : Certified (graph core4299) (root 9) 2 2 :=
  of_native_maps core4299 DegreeTwoThreeSpectrum4718.graph DegreeTwoThreeSpectrum4251.graph
    sourceMap4299 fusedMap4299 sourceMap4299_checked fusedMap4299_checked
    DegreeTwoThreeFiniteComparisons.comparison4299
#print axioms sourceMap4299_checked
#print axioms fusedMap4299_checked
#print axioms certified4299
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
