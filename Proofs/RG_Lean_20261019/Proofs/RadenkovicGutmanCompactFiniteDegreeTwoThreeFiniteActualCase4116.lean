/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4116 : Family 8 := level8.get ⟨80,by decide⟩
def sourceMap4116 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap4116 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4116_checked : acceptsGraphIso
    (source (graph core4116) (root 8) 2 2) DegreeTwoThreeSpectrum3627.graph sourceMap4116=true := by decide +kernel
theorem fusedMap4116_checked : acceptsGraphIso
    (fused (graph core4116) (root 8) 2 2) DegreeTwoThreeSpectrum2396.graph fusedMap4116=true := by decide +kernel
theorem certified4116 : Certified (graph core4116) (root 8) 2 2 :=
  of_native_maps core4116 DegreeTwoThreeSpectrum3627.graph DegreeTwoThreeSpectrum2396.graph
    sourceMap4116 fusedMap4116 sourceMap4116_checked fusedMap4116_checked
    DegreeTwoThreeFiniteComparisons.comparison4116
#print axioms sourceMap4116_checked
#print axioms fusedMap4116_checked
#print axioms certified4116
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
