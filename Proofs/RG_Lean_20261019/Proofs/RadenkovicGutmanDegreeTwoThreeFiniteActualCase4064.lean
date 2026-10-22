/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4064 : Family 7 := level7.get ⟨23,by decide⟩
def sourceMap4064 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,8,2,3,4,5,6,7] (sourceLabel 7 2 2 v)
def fusedMap4064 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4064_checked : acceptsGraphIso
    (source (graph core4064) (root 7) 2 2) DegreeTwoThreeSpectrum2186.graph sourceMap4064=true := by decide +kernel
theorem fusedMap4064_checked : acceptsGraphIso
    (fused (graph core4064) (root 7) 2 2) DegreeTwoThreeSpectrum1731.graph fusedMap4064=true := by decide +kernel
theorem certified4064 : Certified (graph core4064) (root 7) 2 2 :=
  of_native_maps core4064 DegreeTwoThreeSpectrum2186.graph DegreeTwoThreeSpectrum1731.graph
    sourceMap4064 fusedMap4064 sourceMap4064_checked fusedMap4064_checked
    DegreeTwoThreeFiniteComparisons.comparison4064
#print axioms sourceMap4064_checked
#print axioms fusedMap4064_checked
#print axioms certified4064
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
