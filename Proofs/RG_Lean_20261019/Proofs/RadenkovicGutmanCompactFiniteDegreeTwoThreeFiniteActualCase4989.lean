/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4989 : Family 10 := level10.get ⟨1591,by decide⟩
def sourceMap4989 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4989 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4989_checked : acceptsGraphIso
    (source (graph core4989) (root 10) 2 2) DegreeTwoThreeSpectrum7590.graph sourceMap4989=true := by decide +kernel
theorem fusedMap4989_checked : acceptsGraphIso
    (fused (graph core4989) (root 10) 2 2) DegreeTwoThreeSpectrum6090.graph fusedMap4989=true := by decide +kernel
theorem certified4989 : Certified (graph core4989) (root 10) 2 2 :=
  of_native_maps core4989 DegreeTwoThreeSpectrum7590.graph DegreeTwoThreeSpectrum6090.graph
    sourceMap4989 fusedMap4989 sourceMap4989_checked fusedMap4989_checked
    DegreeTwoThreeFiniteComparisons.comparison4989
#print axioms sourceMap4989_checked
#print axioms fusedMap4989_checked
#print axioms certified4989
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
