/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4165 : Family 8 := level8.get ⟨203,by decide⟩
def sourceMap4165 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap4165 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4165_checked : acceptsGraphIso
    (source (graph core4165) (root 8) 2 2) DegreeTwoThreeSpectrum3780.graph sourceMap4165=true := by decide +kernel
theorem fusedMap4165_checked : acceptsGraphIso
    (fused (graph core4165) (root 8) 2 2) DegreeTwoThreeSpectrum2473.graph fusedMap4165=true := by decide +kernel
theorem certified4165 : Certified (graph core4165) (root 8) 2 2 :=
  of_native_maps core4165 DegreeTwoThreeSpectrum3780.graph DegreeTwoThreeSpectrum2473.graph
    sourceMap4165 fusedMap4165 sourceMap4165_checked fusedMap4165_checked
    DegreeTwoThreeFiniteComparisons.comparison4165
#print axioms sourceMap4165_checked
#print axioms fusedMap4165_checked
#print axioms certified4165
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
