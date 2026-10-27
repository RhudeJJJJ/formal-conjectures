/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4097 : Family 8 := level8.get ⟨7,by decide⟩
def sourceMap4097 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,10,11,12,13,14,9,3,4,5,6,7,8] (sourceLabel 8 2 2 v)
def fusedMap4097 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,7,1,2,3,4,5,6] (fusedLabel 8 2 2 v)
theorem sourceMap4097_checked : acceptsGraphIso
    (source (graph core4097) (root 8) 2 2) DegreeTwoThreeSpectrum2819.graph sourceMap4097=true := by decide +kernel
theorem fusedMap4097_checked : acceptsGraphIso
    (fused (graph core4097) (root 8) 2 2) DegreeTwoThreeSpectrum2314.graph fusedMap4097=true := by decide +kernel
theorem certified4097 : Certified (graph core4097) (root 8) 2 2 :=
  of_native_maps core4097 DegreeTwoThreeSpectrum2819.graph DegreeTwoThreeSpectrum2314.graph
    sourceMap4097 fusedMap4097 sourceMap4097_checked fusedMap4097_checked
    DegreeTwoThreeFiniteComparisons.comparison4097
#print axioms sourceMap4097_checked
#print axioms fusedMap4097_checked
#print axioms certified4097
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
