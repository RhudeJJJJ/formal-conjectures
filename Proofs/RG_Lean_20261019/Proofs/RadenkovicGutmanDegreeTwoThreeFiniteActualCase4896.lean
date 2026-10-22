/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4896 : Family 10 := level10.get ⟨1363,by decide⟩
def sourceMap4896 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4896 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4896_checked : acceptsGraphIso
    (source (graph core4896) (root 10) 2 2) DegreeTwoThreeSpectrum7442.graph sourceMap4896=true := by decide +kernel
theorem fusedMap4896_checked : acceptsGraphIso
    (fused (graph core4896) (root 10) 2 2) DegreeTwoThreeSpectrum6700.graph fusedMap4896=true := by decide +kernel
theorem certified4896 : Certified (graph core4896) (root 10) 2 2 :=
  of_native_maps core4896 DegreeTwoThreeSpectrum7442.graph DegreeTwoThreeSpectrum6700.graph
    sourceMap4896 fusedMap4896 sourceMap4896_checked fusedMap4896_checked
    DegreeTwoThreeFiniteComparisons.comparison4896
#print axioms sourceMap4896_checked
#print axioms fusedMap4896_checked
#print axioms certified4896
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
