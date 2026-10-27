/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4200 : Family 9 := level9.get ⟨41,by decide⟩
def sourceMap4200 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,11,12,13,14,15,9,10,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap4200 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,9,10,11,12,13,14,15,7,8,1,2,3,4,5,6] (fusedLabel 9 2 2 v)
theorem sourceMap4200_checked : acceptsGraphIso
    (source (graph core4200) (root 9) 2 2) DegreeTwoThreeSpectrum4544.graph sourceMap4200=true := by decide +kernel
theorem fusedMap4200_checked : acceptsGraphIso
    (fused (graph core4200) (root 9) 2 2) DegreeTwoThreeSpectrum3888.graph fusedMap4200=true := by decide +kernel
theorem certified4200 : Certified (graph core4200) (root 9) 2 2 :=
  of_native_maps core4200 DegreeTwoThreeSpectrum4544.graph DegreeTwoThreeSpectrum3888.graph
    sourceMap4200 fusedMap4200 sourceMap4200_checked fusedMap4200_checked
    DegreeTwoThreeFiniteComparisons.comparison4200
#print axioms sourceMap4200_checked
#print axioms fusedMap4200_checked
#print axioms certified4200
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
