/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4314 : Family 9 := level9.get ⟨392,by decide⟩
def sourceMap4314 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4314 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4314_checked : acceptsGraphIso
    (source (graph core4314) (root 9) 2 2) DegreeTwoThreeSpectrum4770.graph sourceMap4314=true := by decide +kernel
theorem fusedMap4314_checked : acceptsGraphIso
    (fused (graph core4314) (root 9) 2 2) DegreeTwoThreeSpectrum4345.graph fusedMap4314=true := by decide +kernel
theorem certified4314 : Certified (graph core4314) (root 9) 2 2 :=
  of_native_maps core4314 DegreeTwoThreeSpectrum4770.graph DegreeTwoThreeSpectrum4345.graph
    sourceMap4314 fusedMap4314 sourceMap4314_checked fusedMap4314_checked
    DegreeTwoThreeFiniteComparisons.comparison4314
#print axioms sourceMap4314_checked
#print axioms fusedMap4314_checked
#print axioms certified4314
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
