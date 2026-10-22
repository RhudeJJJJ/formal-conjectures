/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4462 : Family 10 := level10.get ⟨154,by decide⟩
def sourceMap4462 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4462 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4462_checked : acceptsGraphIso
    (source (graph core4462) (root 10) 2 2) DegreeTwoThreeSpectrum6854.graph sourceMap4462=true := by decide +kernel
theorem fusedMap4462_checked : acceptsGraphIso
    (fused (graph core4462) (root 10) 2 2) DegreeTwoThreeSpectrum5090.graph fusedMap4462=true := by decide +kernel
theorem certified4462 : Certified (graph core4462) (root 10) 2 2 :=
  of_native_maps core4462 DegreeTwoThreeSpectrum6854.graph DegreeTwoThreeSpectrum5090.graph
    sourceMap4462 fusedMap4462 sourceMap4462_checked fusedMap4462_checked
    DegreeTwoThreeFiniteComparisons.comparison4462
#print axioms sourceMap4462_checked
#print axioms fusedMap4462_checked
#print axioms certified4462
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
