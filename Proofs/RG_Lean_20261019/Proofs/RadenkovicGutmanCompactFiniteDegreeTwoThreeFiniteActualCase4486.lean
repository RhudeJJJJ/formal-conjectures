/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4486 : Family 10 := level10.get ⟨238,by decide⟩
def sourceMap4486 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4486 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4486_checked : acceptsGraphIso
    (source (graph core4486) (root 10) 2 2) DegreeTwoThreeSpectrum6330.graph sourceMap4486=true := by decide +kernel
theorem fusedMap4486_checked : acceptsGraphIso
    (fused (graph core4486) (root 10) 2 2) DegreeTwoThreeSpectrum5303.graph fusedMap4486=true := by decide +kernel
theorem certified4486 : Certified (graph core4486) (root 10) 2 2 :=
  of_native_maps core4486 DegreeTwoThreeSpectrum6330.graph DegreeTwoThreeSpectrum5303.graph
    sourceMap4486 fusedMap4486 sourceMap4486_checked fusedMap4486_checked
    DegreeTwoThreeFiniteComparisons.comparison4486
#print axioms sourceMap4486_checked
#print axioms fusedMap4486_checked
#print axioms certified4486
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
