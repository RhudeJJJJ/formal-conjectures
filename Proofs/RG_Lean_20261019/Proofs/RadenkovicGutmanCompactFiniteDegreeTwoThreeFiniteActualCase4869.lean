/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4869 : Family 10 := level10.get ⟨1299,by decide⟩
def sourceMap4869 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4869 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4869_checked : acceptsGraphIso
    (source (graph core4869) (root 10) 2 2) DegreeTwoThreeSpectrum7380.graph sourceMap4869=true := by decide +kernel
theorem fusedMap4869_checked : acceptsGraphIso
    (fused (graph core4869) (root 10) 2 2) DegreeTwoThreeSpectrum6585.graph fusedMap4869=true := by decide +kernel
theorem certified4869 : Certified (graph core4869) (root 10) 2 2 :=
  of_native_maps core4869 DegreeTwoThreeSpectrum7380.graph DegreeTwoThreeSpectrum6585.graph
    sourceMap4869 fusedMap4869 sourceMap4869_checked fusedMap4869_checked
    DegreeTwoThreeFiniteComparisons.comparison4869
#print axioms sourceMap4869_checked
#print axioms fusedMap4869_checked
#print axioms certified4869
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
